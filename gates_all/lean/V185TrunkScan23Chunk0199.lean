import V185TrunkScan23Chunk0198

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1177923 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 1, 4]
def baseStart_1177923 : Nat := 118140960795 + 1177923 * 2 ^ 59
def prefixEnd_1177923 : Nat := 4983230072969 + 3 ^ 40 * 1177923 * 2
def baseEnd_1177923 : Nat := 201613557662033368181779

theorem tailTrace_1177923 : CollatzResearch.WordTrace tailWord_1177923 prefixEnd_1177923 201613557662033368181779 := by
  unfold tailWord_1177923
  simp only [CollatzResearch.WordTrace]
  refine ⟨42962381311593619077290423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28641587541062412718193615 42962381311593619077290423)
  ·
    refine ⟨64443571967390428615935635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42962381311593619077290423 64443571967390428615935635)
    ·
      refine ⟨96665357951085642923903453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64443571967390428615935635 96665357951085642923903453)
      ·
        refine ⟨36249509231657116096463795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96665357951085642923903453 36249509231657116096463795)
        ·
          refine ⟨54374263847485674144695693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36249509231657116096463795 54374263847485674144695693)
          ·
            refine ⟨20390348942807127804260885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54374263847485674144695693 20390348942807127804260885)
            ·
              refine ⟨955797606694084115824729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20390348942807127804260885 955797606694084115824729)
              ·
                refine ⟨716848205020563086868547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955797606694084115824729 716848205020563086868547)
                ·
                  refine ⟨1075272307530844630302821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716848205020563086868547 1075272307530844630302821)
                  ·
                    refine ⟨201613557662033368181779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1075272307530844630302821 201613557662033368181779)
                    ·
                      rfl

theorem cell23_1177923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 4].length) (baseStart_1177923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177923 prefixEnd_1177923 := by exact prefixLift 1177923
  have htrace : WordTrace (prefixWord ++ tailWord_1177923) baseStart_1177923 baseEnd_1177923 := by
    simpa [prefixWord, tailWord_1177923, baseEnd_1177923] using wordTrace_append hprefix tailTrace_1177923
  have hstable : (prefixWord ++ tailWord_1177923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177923).length < 2 ^ (prefixWord ++ tailWord_1177923).sum := by decide
  have hdescent : baseEnd_1177923 < baseStart_1177923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177956 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_1177956 : Nat := 118140960795 + 1177956 * 2 ^ 59
def prefixEnd_1177956 : Nat := 4983230072969 + 3 ^ 40 * 1177956 * 2
def baseEnd_1177956 : Nat := 604857617847698475432685

theorem tailTrace_1177956 : CollatzResearch.WordTrace tailWord_1177956 prefixEnd_1177956 604857617847698475432685 := by
  unfold tailWord_1177956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21481792460237032856620861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28642389946982710475494481 21481792460237032856620861)
  ·
    refine ⟨8055672172588887321232823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21481792460237032856620861 8055672172588887321232823)
    ·
      refine ⟨12083508258883330981849235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8055672172588887321232823 12083508258883330981849235)
      ·
        refine ⟨18125262388324996472773853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12083508258883330981849235 18125262388324996472773853)
        ·
          refine ⟨6796973395621873677290195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18125262388324996472773853 6796973395621873677290195)
          ·
            refine ⟨10195460093432810515935293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796973395621873677290195 10195460093432810515935293)
            ·
              refine ⟨3823297535037303943475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10195460093432810515935293 3823297535037303943475735)
              ·
                refine ⟨5734946302555955915213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823297535037303943475735 5734946302555955915213603)
                ·
                  refine ⟨8602419453833933872820405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734946302555955915213603 8602419453833933872820405)
                  ·
                    refine ⟨806476823796931300576913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8602419453833933872820405 806476823796931300576913)
                    ·
                      refine ⟨604857617847698475432685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806476823796931300576913 604857617847698475432685)
                      ·
                        rfl

theorem cell23_1177956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_1177956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177956 prefixEnd_1177956 := by exact prefixLift 1177956
  have htrace : WordTrace (prefixWord ++ tailWord_1177956) baseStart_1177956 baseEnd_1177956 := by
    simpa [prefixWord, tailWord_1177956, baseEnd_1177956] using wordTrace_append hprefix tailTrace_1177956
  have hstable : (prefixWord ++ tailWord_1177956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177956).length < 2 ^ (prefixWord ++ tailWord_1177956).sum := by decide
  have hdescent : baseEnd_1177956 < baseStart_1177956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177996 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_1177996 : Nat := 118140960795 + 1177996 * 2 ^ 59
def prefixEnd_1177996 : Nat := 4983230072969 + 3 ^ 40 * 1177996 * 2
def baseEnd_1177996 : Nat := 201626052357959439644167

theorem tailTrace_1177996 : CollatzResearch.WordTrace tailWord_1177996 prefixEnd_1177996 201626052357959439644167 := by
  unfold tailWord_1177996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21482521920164576272348921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28643362560219435029798561 21482521920164576272348921)
  ·
    refine ⟨16111891440123432204261691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21482521920164576272348921 16111891440123432204261691)
    ·
      refine ⟨24167837160185148306392537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16111891440123432204261691 24167837160185148306392537)
      ·
        refine ⟨18125877870138861229794403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24167837160185148306392537 18125877870138861229794403)
        ·
          refine ⟨27188816805208291844691605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18125877870138861229794403 27188816805208291844691605)
          ·
            refine ⟨1274475787744138680219919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27188816805208291844691605 1274475787744138680219919)
            ·
              refine ⟨1911713681616208020329879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274475787744138680219919 1911713681616208020329879)
              ·
                refine ⟨2867570522424312030494819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911713681616208020329879 2867570522424312030494819)
                ·
                  refine ⟨4301355783636468045742229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867570522424312030494819 4301355783636468045742229)
                  ·
                    refine ⟨201626052357959439644167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4301355783636468045742229 201626052357959439644167)
                    ·
                      rfl

theorem cell23_1177996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_1177996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177996 prefixEnd_1177996 := by exact prefixLift 1177996
  have htrace : WordTrace (prefixWord ++ tailWord_1177996) baseStart_1177996 baseEnd_1177996 := by
    simpa [prefixWord, tailWord_1177996, baseEnd_1177996] using wordTrace_append hprefix tailTrace_1177996
  have hstable : (prefixWord ++ tailWord_1177996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177996).length < 2 ^ (prefixWord ++ tailWord_1177996).sum := by decide
  have hdescent : baseEnd_1177996 < baseStart_1177996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178014 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1178014 : Nat := 118140960795 + 1178014 * 2 ^ 59
def prefixEnd_1178014 : Nat := 4983230072969 + 3 ^ 40 * 1178014 * 2
def baseEnd_1178014 : Nat := 604887399725659248507419

theorem tailTrace_1178014 : CollatzResearch.WordTrace tailWord_1178014 prefixEnd_1178014 604887399725659248507419 := by
  unfold tailWord_1178014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370712544282992702356637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28643800236175961079235397 5370712544282992702356637)
  ·
    refine ⟨2014017204106122263383739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5370712544282992702356637 2014017204106122263383739)
    ·
      refine ⟨3021025806159183395075609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014017204106122263383739 3021025806159183395075609)
      ·
        refine ⟨2265769354619387546306707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021025806159183395075609 2265769354619387546306707)
        ·
          refine ⟨3398654031929081319460061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265769354619387546306707 3398654031929081319460061)
          ·
            refine ⟨1274495261973405494797523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3398654031929081319460061 1274495261973405494797523)
            ·
              refine ⟨1911742892960108242196285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274495261973405494797523 1911742892960108242196285)
              ·
                refine ⟨716903584860040590823607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911742892960108242196285 716903584860040590823607)
                ·
                  refine ⟨1075355377290060886235411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716903584860040590823607 1075355377290060886235411)
                  ·
                    refine ⟨1613033065935091329353117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075355377290060886235411 1613033065935091329353117)
                    ·
                      refine ⟨604887399725659248507419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613033065935091329353117 604887399725659248507419)
                      ·
                        rfl

theorem cell23_1178014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1178014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178014 prefixEnd_1178014 := by exact prefixLift 1178014
  have htrace : WordTrace (prefixWord ++ tailWord_1178014) baseStart_1178014 baseEnd_1178014 := by
    simpa [prefixWord, tailWord_1178014, baseEnd_1178014] using wordTrace_append hprefix tailTrace_1178014
  have hstable : (prefixWord ++ tailWord_1178014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178014).length < 2 ^ (prefixWord ++ tailWord_1178014).sum := by decide
  have hdescent : baseEnd_1178014 < baseStart_1178014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178023 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1178023 : Nat := 118140960795 + 1178023 * 2 ^ 59
def prefixEnd_1178023 : Nat := 4983230072969 + 3 ^ 40 * 1178023 * 2
def baseEnd_1178023 : Nat := 604892021051549713294877

theorem tailTrace_1178023 : CollatzResearch.WordTrace tailWord_1178023 prefixEnd_1178023 604892021051549713294877 := by
  unfold tailWord_1178023
  simp only [CollatzResearch.WordTrace]
  refine ⟨42966028611231336155930723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28644019074154224103953815 42966028611231336155930723)
  ·
    refine ⟨64449042916847004233896085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42966028611231336155930723 64449042916847004233896085)
    ·
      refine ⟨3021048886727203323463879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64449042916847004233896085 3021048886727203323463879)
      ·
        refine ⟨4531573330090804985195819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021048886727203323463879 4531573330090804985195819)
        ·
          refine ⟨6797359995136207477793729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531573330090804985195819 6797359995136207477793729)
          ·
            refine ⟨5098019996352155608345297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6797359995136207477793729 5098019996352155608345297)
            ·
              refine ⟨3823514997264116706258973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098019996352155608345297 3823514997264116706258973)
              ·
                refine ⟨1433818123974043764847115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3823514997264116706258973 1433818123974043764847115)
                ·
                  refine ⟨2150727185961065647270673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433818123974043764847115 2150727185961065647270673)
                  ·
                    refine ⟨1613045389470799235453005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150727185961065647270673 1613045389470799235453005)
                    ·
                      refine ⟨604892021051549713294877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613045389470799235453005 604892021051549713294877)
                      ·
                        rfl

theorem cell23_1178023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1178023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178023 prefixEnd_1178023 := by exact prefixLift 1178023
  have htrace : WordTrace (prefixWord ++ tailWord_1178023) baseStart_1178023 baseEnd_1178023 := by
    simpa [prefixWord, tailWord_1178023, baseEnd_1178023] using wordTrace_append hprefix tailTrace_1178023
  have hstable : (prefixWord ++ tailWord_1178023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178023).length < 2 ^ (prefixWord ++ tailWord_1178023).sum := by decide
  have hdescent : baseEnd_1178023 < baseStart_1178023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178037 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_1178037 : Nat := 118140960795 + 1178037 * 2 ^ 59
def prefixEnd_1178037 : Nat := 4983230072969 + 3 ^ 40 * 1178037 * 2
def baseEnd_1178037 : Nat := 604899209780712658519813

theorem tailTrace_1178037 : CollatzResearch.WordTrace tailWord_1178037 prefixEnd_1178037 604899209780712658519813 := by
  unfold tailWord_1178037
  simp only [CollatzResearch.WordTrace]
  refine ⟨42966539233180616546940365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28644359488787077697960243 42966539233180616546940365)
  ·
    refine ⟨16112452212442731205102637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42966539233180616546940365 16112452212442731205102637)
    ·
      refine ⟨6042169579666024201913489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16112452212442731205102637 6042169579666024201913489)
      ·
        refine ⟨4531627184749518151435117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6042169579666024201913489 4531627184749518151435117)
        ·
          refine ⟨1699360194281069306788169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4531627184749518151435117 1699360194281069306788169)
          ·
            refine ⟨1274520145710801980091127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699360194281069306788169 1274520145710801980091127)
            ·
              refine ⟨1911780218566202970136691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274520145710801980091127 1911780218566202970136691)
              ·
                refine ⟨2867670327849304455205037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911780218566202970136691 2867670327849304455205037)
                ·
                  refine ⟨1075376372943489170701889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2867670327849304455205037 1075376372943489170701889)
                  ·
                    refine ⟨806532279707616878026417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1075376372943489170701889 806532279707616878026417)
                    ·
                      refine ⟨604899209780712658519813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806532279707616878026417 604899209780712658519813)
                      ·
                        rfl

theorem cell23_1178037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_1178037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178037 prefixEnd_1178037 := by exact prefixLift 1178037
  have htrace : WordTrace (prefixWord ++ tailWord_1178037) baseStart_1178037 baseEnd_1178037 := by
    simpa [prefixWord, tailWord_1178037, baseEnd_1178037] using wordTrace_append hprefix tailTrace_1178037
  have hstable : (prefixWord ++ tailWord_1178037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178037).length < 2 ^ (prefixWord ++ tailWord_1178037).sum := by decide
  have hdescent : baseEnd_1178037 < baseStart_1178037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178080 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2]
def baseStart_1178080 : Nat := 118140960795 + 1178080 * 2 ^ 59
def prefixEnd_1178080 : Nat := 4983230072969 + 3 ^ 40 * 1178080 * 2
def baseEnd_1178080 : Nat := 604921289448855990282115

theorem tailTrace_1178080 : CollatzResearch.WordTrace tailWord_1178080 prefixEnd_1178080 604921289448855990282115 := by
  unfold tailWord_1178080
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484053786012417445377847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28645405048016556593837129 21484053786012417445377847)
  ·
    refine ⟨32226080679018626168066771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21484053786012417445377847 32226080679018626168066771)
    ·
      refine ⟨48339121018527939252100157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32226080679018626168066771 48339121018527939252100157)
      ·
        refine ⟨18127170381947977219537559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48339121018527939252100157 18127170381947977219537559)
        ·
          refine ⟨27190755572921965829306339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18127170381947977219537559 27190755572921965829306339)
          ·
            refine ⟨40786133359382948743959509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27190755572921965829306339 40786133359382948743959509)
            ·
              refine ⟨955925000610537861186551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40786133359382948743959509 955925000610537861186551)
              ·
                refine ⟨1433887500915806791779827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955925000610537861186551 1433887500915806791779827)
                ·
                  refine ⟨2150831251373710187669741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433887500915806791779827 2150831251373710187669741)
                  ·
                    refine ⟨806561719265141320376153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150831251373710187669741 806561719265141320376153)
                    ·
                      refine ⟨604921289448855990282115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806561719265141320376153 604921289448855990282115)
                      ·
                        rfl

theorem cell23_1178080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_1178080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178080 prefixEnd_1178080 := by exact prefixLift 1178080
  have htrace : WordTrace (prefixWord ++ tailWord_1178080) baseStart_1178080 baseEnd_1178080 := by
    simpa [prefixWord, tailWord_1178080, baseEnd_1178080] using wordTrace_append hprefix tailTrace_1178080
  have hstable : (prefixWord ++ tailWord_1178080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178080).length < 2 ^ (prefixWord ++ tailWord_1178080).sum := by decide
  have hdescent : baseEnd_1178080 < baseStart_1178080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178099 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 7]
def baseStart_1178099 : Nat := 118140960795 + 1178099 * 2 ^ 59
def prefixEnd_1178099 : Nat := 4983230072969 + 3 ^ 40 * 1178099 * 2
def baseEnd_1178099 : Nat := 67214560620143490660503

theorem tailTrace_1178099 : CollatzResearch.WordTrace tailWord_1178099 prefixEnd_1178099 67214560620143490660503 := by
  unfold tailWord_1178099
  simp only [CollatzResearch.WordTrace]
  refine ⟨42968800558956001135697351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28645867039304000757131567 42968800558956001135697351)
  ·
    refine ⟨64453200838434001703546027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42968800558956001135697351 64453200838434001703546027)
    ·
      refine ⟨96679801257651002555319041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64453200838434001703546027 96679801257651002555319041)
      ·
        refine ⟨72509850943238251916489281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96679801257651002555319041 72509850943238251916489281)
        ·
          refine ⟨54382388207428688937366961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72509850943238251916489281 54382388207428688937366961)
          ·
            refine ⟨40786791155571516703025221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54382388207428688937366961 40786791155571516703025221)
            ·
              refine ⟨7647523341669659381817229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40786791155571516703025221 7647523341669659381817229)
              ·
                refine ⟨2867821253126122268181461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7647523341669659381817229 2867821253126122268181461)
                ·
                  refine ⟨67214560620143490660503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2867821253126122268181461 67214560620143490660503)
                  ·
                    rfl

theorem cell23_1178099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 7].length) (baseStart_1178099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178099 prefixEnd_1178099 := by exact prefixLift 1178099
  have htrace : WordTrace (prefixWord ++ tailWord_1178099) baseStart_1178099 baseEnd_1178099 := by
    simpa [prefixWord, tailWord_1178099, baseEnd_1178099] using wordTrace_append hprefix tailTrace_1178099
  have hstable : (prefixWord ++ tailWord_1178099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178099).length < 2 ^ (prefixWord ++ tailWord_1178099).sum := by decide
  have hdescent : baseEnd_1178099 < baseStart_1178099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178116 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1178116 : Nat := 118140960795 + 1178116 * 2 ^ 59
def prefixEnd_1178116 : Nat := 4983230072969 + 3 ^ 40 * 1178116 * 2
def baseEnd_1178116 : Nat := 67215530528046427714661

theorem tailTrace_1178116 : CollatzResearch.WordTrace tailWord_1178116 prefixEnd_1178116 67215530528046427714661 := by
  unfold tailWord_1178116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484710299947206519533101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28646280399929608692710801 21484710299947206519533101)
  ·
    refine ⟨8056766362480202444824913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21484710299947206519533101 8056766362480202444824913)
    ·
      refine ⟨6042574771860151833618685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8056766362480202444824913 6042574771860151833618685)
      ·
        refine ⟨2265965539447556937607007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6042574771860151833618685 2265965539447556937607007)
        ·
          refine ⟨3398948309171335406410511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265965539447556937607007 3398948309171335406410511)
          ·
            refine ⟨5098422463757003109615767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398948309171335406410511 5098422463757003109615767)
            ·
              refine ⟨7647633695635504664423651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098422463757003109615767 7647633695635504664423651)
              ·
                refine ⟨11471450543453256996635477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7647633695635504664423651 11471450543453256996635477)
                ·
                  refine ⟨67215530528046427714661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11471450543453256996635477 67215530528046427714661)
                  ·
                    rfl

theorem cell23_1178116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1178116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178116 prefixEnd_1178116 := by exact prefixLift 1178116
  have htrace : WordTrace (prefixWord ++ tailWord_1178116) baseStart_1178116 baseEnd_1178116 := by
    simpa [prefixWord, tailWord_1178116, baseEnd_1178116] using wordTrace_append hprefix tailTrace_1178116
  have hstable : (prefixWord ++ tailWord_1178116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178116).length < 2 ^ (prefixWord ++ tailWord_1178116).sum := by decide
  have hdescent : baseEnd_1178116 < baseStart_1178116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178133 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 5]
def baseStart_1178133 : Nat := 118140960795 + 1178133 * 2 ^ 59
def prefixEnd_1178133 : Nat := 4983230072969 + 3 ^ 40 * 1178133 * 2
def baseEnd_1178133 : Nat := 67216500435949364768819

theorem tailTrace_1178133 : CollatzResearch.WordTrace tailWord_1178133 prefixEnd_1178133 67216500435949364768819 := by
  unfold tailWord_1178133
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970040640832824942435053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28646693760555216628290035 42970040640832824942435053)
  ·
    refine ⟨16113765240312309353413145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42970040640832824942435053 16113765240312309353413145)
    ·
      refine ⟨12085323930234232015059859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16113765240312309353413145 12085323930234232015059859)
      ·
        refine ⟨18127985895351348022589789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085323930234232015059859 18127985895351348022589789)
        ·
          refine ⟨6797994710756755508471171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18127985895351348022589789 6797994710756755508471171)
          ·
            refine ⟨10196992066135133262706757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797994710756755508471171 10196992066135133262706757)
            ·
              refine ⟨1911936012400337486757517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10196992066135133262706757 1911936012400337486757517)
              ·
                refine ⟨716976004650126557534069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911936012400337486757517 716976004650126557534069)
                ·
                  refine ⟨67216500435949364768819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716976004650126557534069 67216500435949364768819)
                  ·
                    rfl

theorem cell23_1178133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_1178133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178133 prefixEnd_1178133 := by exact prefixLift 1178133
  have htrace : WordTrace (prefixWord ++ tailWord_1178133) baseStart_1178133 baseEnd_1178133 := by
    simpa [prefixWord, tailWord_1178133, baseEnd_1178133] using wordTrace_append hprefix tailTrace_1178133
  have hstable : (prefixWord ++ tailWord_1178133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178133).length < 2 ^ (prefixWord ++ tailWord_1178133).sum := by decide
  have hdescent : baseEnd_1178133 < baseStart_1178133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178144 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1178144 : Nat := 118140960795 + 1178144 * 2 ^ 59
def prefixEnd_1178144 : Nat := 4983230072969 + 3 ^ 40 * 1178144 * 2
def baseEnd_1178144 : Nat := 604954152210743739881821

theorem tailTrace_1178144 : CollatzResearch.WordTrace tailWord_1178144 prefixEnd_1178144 604954152210743739881821 := by
  unfold tailWord_1178144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485220921896486910542743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28646961229195315880723657 21485220921896486910542743)
  ·
    refine ⟨32227831382844730365814115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21485220921896486910542743 32227831382844730365814115)
    ·
      refine ⟨48341747074267095548721173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32227831382844730365814115 48341747074267095548721173)
      ·
        refine ⟨2266019394106270103846305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48341747074267095548721173 2266019394106270103846305)
        ·
          refine ⟨1699514545579702577884729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2266019394106270103846305 1699514545579702577884729)
          ·
            refine ⟨1274635909184776933413547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699514545579702577884729 1274635909184776933413547)
            ·
              refine ⟨1911953863777165400120321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274635909184776933413547 1911953863777165400120321)
              ·
                refine ⟨1433965397832874050090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911953863777165400120321 1433965397832874050090241)
                ·
                  refine ⟨1075474048374655537567681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433965397832874050090241 1075474048374655537567681)
                  ·
                    refine ⟨806605536280991653175761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1075474048374655537567681 806605536280991653175761)
                    ·
                      refine ⟨604954152210743739881821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806605536280991653175761 604954152210743739881821)
                      ·
                        rfl

theorem cell23_1178144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1178144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178144 prefixEnd_1178144 := by exact prefixLift 1178144
  have htrace : WordTrace (prefixWord ++ tailWord_1178144) baseStart_1178144 baseEnd_1178144 := by
    simpa [prefixWord, tailWord_1178144, baseEnd_1178144] using wordTrace_append hprefix tailTrace_1178144
  have hstable : (prefixWord ++ tailWord_1178144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178144).length < 2 ^ (prefixWord ++ tailWord_1178144).sum := by decide
  have hdescent : baseEnd_1178144 < baseStart_1178144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178146 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1178146 : Nat := 118140960795 + 1178146 * 2 ^ 59
def prefixEnd_1178146 : Nat := 4983230072969 + 3 ^ 40 * 1178146 * 2
def baseEnd_1178146 : Nat := 201651726390684244018937

theorem tailTrace_1178146 : CollatzResearch.WordTrace tailWord_1178146 prefixEnd_1178146 201651726390684244018937 := by
  unfold tailWord_1178146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742628697446432040664573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28647009859857152108438861 10742628697446432040664573)
  ·
    refine ⟨4028485761542412015249215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10742628697446432040664573 4028485761542412015249215)
    ·
      refine ⟨6042728642313618022873823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028485761542412015249215 6042728642313618022873823)
      ·
        refine ⟨9064092963470427034310735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042728642313618022873823 9064092963470427034310735)
        ·
          refine ⟨13596139445205640551466103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064092963470427034310735 13596139445205640551466103)
          ·
            refine ⟨20394209167808460827199155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596139445205640551466103 20394209167808460827199155)
            ·
              refine ⟨30591313751712691240798733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20394209167808460827199155 30591313751712691240798733)
              ·
                refine ⟨11471742656892259215299525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30591313751712691240798733 11471742656892259215299525)
                ·
                  refine ⟨2150951748167298602868661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11471742656892259215299525 2150951748167298602868661)
                  ·
                    refine ⟨201651726390684244018937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2150951748167298602868661 201651726390684244018937)
                    ·
                      rfl

theorem cell23_1178146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1178146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178146 prefixEnd_1178146 := by exact prefixLift 1178146
  have htrace : WordTrace (prefixWord ++ tailWord_1178146) baseStart_1178146 baseEnd_1178146 := by
    simpa [prefixWord, tailWord_1178146, baseEnd_1178146] using wordTrace_append hprefix tailTrace_1178146
  have hstable : (prefixWord ++ tailWord_1178146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178146).length < 2 ^ (prefixWord ++ tailWord_1178146).sum := by decide
  have hdescent : baseEnd_1178146 < baseStart_1178146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178223 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 6]
def baseStart_1178223 : Nat := 118140960795 + 1178223 * 2 ^ 59
def prefixEnd_1178223 : Nat := 4983230072969 + 3 ^ 40 * 1178223 * 2
def baseEnd_1178223 : Nat := 67221635242494325643773

theorem tailTrace_1178223 : CollatzResearch.WordTrace tailWord_1178223 prefixEnd_1178223 67221635242494325643773 := by
  unfold tailWord_1178223
  simp only [CollatzResearch.WordTrace]
  refine ⟨42973323210506770313211323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28648882140337846875474215 42973323210506770313211323)
  ·
    refine ⟨64459984815760155469816985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42973323210506770313211323 64459984815760155469816985)
    ·
      refine ⟨48344988611820116602362739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64459984815760155469816985 48344988611820116602362739)
      ·
        refine ⟨72517482917730174903544109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48344988611820116602362739 72517482917730174903544109)
        ·
          refine ⟨27194056094148815588829041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72517482917730174903544109 27194056094148815588829041)
          ·
            refine ⟨20395542070611611691621781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27194056094148815588829041 20395542070611611691621781)
            ·
              refine ⟨956041034559919298044771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20395542070611611691621781 956041034559919298044771)
              ·
                refine ⟨1434061551839878947067157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956041034559919298044771 1434061551839878947067157)
                ·
                  refine ⟨67221635242494325643773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1434061551839878947067157 67221635242494325643773)
                  ·
                    rfl

theorem cell23_1178223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 6].length) (baseStart_1178223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178223 prefixEnd_1178223 := by exact prefixLift 1178223
  have htrace : WordTrace (prefixWord ++ tailWord_1178223) baseStart_1178223 baseEnd_1178223 := by
    simpa [prefixWord, tailWord_1178223, baseEnd_1178223] using wordTrace_append hprefix tailTrace_1178223
  have hstable : (prefixWord ++ tailWord_1178223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178223).length < 2 ^ (prefixWord ++ tailWord_1178223).sum := by decide
  have hdescent : baseEnd_1178223 < baseStart_1178223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178243 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 5, 2]
def baseStart_1178243 : Nat := 118140960795 + 1178243 * 2 ^ 59
def prefixEnd_1178243 : Nat := 4983230072969 + 3 ^ 40 * 1178243 * 2
def baseEnd_1178243 : Nat := 605004986795538852543865

theorem tailTrace_1178243 : CollatzResearch.WordTrace tailWord_1178243 prefixEnd_1178243 605004986795538852543865 := by
  unfold tailWord_1178243
  simp only [CollatzResearch.WordTrace]
  refine ⟨42974052670434313728939383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28649368446956209152626255 42974052670434313728939383)
  ·
    refine ⟨64461079005651470593409075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42974052670434313728939383 64461079005651470593409075)
    ·
      refine ⟨96691618508477205890113613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64461079005651470593409075 96691618508477205890113613)
      ·
        refine ⟨36259356940678952208792605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96691618508477205890113613 36259356940678952208792605)
        ·
          refine ⟨13597258852754607078297227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36259356940678952208792605 13597258852754607078297227)
          ·
            refine ⟨20395888279131910617445841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597258852754607078297227 20395888279131910617445841)
            ·
              refine ⟨15296916209348932963084381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20395888279131910617445841 15296916209348932963084381)
              ·
                refine ⟨5736343578505849861156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15296916209348932963084381 5736343578505849861156643)
                ·
                  refine ⟨8604515367758774791734965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736343578505849861156643 8604515367758774791734965)
                  ·
                    refine ⟨806673315727385136725153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604515367758774791734965 806673315727385136725153)
                    ·
                      refine ⟨605004986795538852543865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806673315727385136725153 605004986795538852543865)
                      ·
                        rfl

theorem cell23_1178243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_1178243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178243 prefixEnd_1178243 := by exact prefixLift 1178243
  have htrace : WordTrace (prefixWord ++ tailWord_1178243) baseStart_1178243 baseEnd_1178243 := by
    simpa [prefixWord, tailWord_1178243, baseEnd_1178243] using wordTrace_append hprefix tailTrace_1178243
  have hstable : (prefixWord ++ tailWord_1178243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178243).length < 2 ^ (prefixWord ++ tailWord_1178243).sum := by decide
  have hdescent : baseEnd_1178243 < baseStart_1178243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178294 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1178294 : Nat := 118140960795 + 1178294 * 2 ^ 59
def prefixEnd_1178294 : Nat := 4983230072969 + 3 ^ 40 * 1178294 * 2
def baseEnd_1178294 : Nat := 605031174308918153006131

theorem tailTrace_1178294 : CollatzResearch.WordTrace tailWord_1178294 prefixEnd_1178294 605031174308918153006131 := by
  unfold tailWord_1178294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685994549578096839940371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28650608528833032959363957 2685994549578096839940371)
  ·
    refine ⟨4028991824367145259910557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2685994549578096839940371 4028991824367145259910557)
    ·
      refine ⟨1510871934137679472466459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4028991824367145259910557 1510871934137679472466459)
      ·
        refine ⟨2266307901206519208699689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510871934137679472466459 2266307901206519208699689)
        ·
          refine ⟨1699730925904889406524767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2266307901206519208699689 1699730925904889406524767)
          ·
            refine ⟨2549596388857334109787151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699730925904889406524767 2549596388857334109787151)
            ·
              refine ⟨3824394583286001164680727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549596388857334109787151 3824394583286001164680727)
              ·
                refine ⟨5736591874929001747021091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824394583286001164680727 5736591874929001747021091)
                ·
                  refine ⟨8604887812393502620531637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736591874929001747021091 8604887812393502620531637)
                  ·
                    refine ⟨806708232411890870674841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604887812393502620531637 806708232411890870674841)
                    ·
                      refine ⟨605031174308918153006131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806708232411890870674841 605031174308918153006131)
                      ·
                        rfl

theorem cell23_1178294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1178294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178294 prefixEnd_1178294 := by exact prefixLift 1178294
  have htrace : WordTrace (prefixWord ++ tailWord_1178294) baseStart_1178294 baseEnd_1178294 := by
    simpa [prefixWord, tailWord_1178294, baseEnd_1178294] using wordTrace_append hprefix tailTrace_1178294
  have hstable : (prefixWord ++ tailWord_1178294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178294).length < 2 ^ (prefixWord ++ tailWord_1178294).sum := by decide
  have hdescent : baseEnd_1178294 < baseStart_1178294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178303 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_1178303 : Nat := 118140960795 + 1178303 * 2 ^ 59
def prefixEnd_1178303 : Nat := 4983230072969 + 3 ^ 40 * 1178303 * 2
def baseEnd_1178303 : Nat := 605035795634808617793589

theorem tailTrace_1178303 : CollatzResearch.WordTrace tailWord_1178303 prefixEnd_1178303 605035795634808617793589 := by
  unfold tailWord_1178303
  simp only [CollatzResearch.WordTrace]
  refine ⟨42976241050216943976123563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28650827366811295984082375 42976241050216943976123563)
  ·
    refine ⟨64464361575325415964185345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42976241050216943976123563 64464361575325415964185345)
    ·
      refine ⟨48348271181494061973139009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64464361575325415964185345 48348271181494061973139009)
      ·
        refine ⟨36261203386120546479854257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48348271181494061973139009 36261203386120546479854257)
        ·
          refine ⟨27195902539590409859890693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36261203386120546479854257 27195902539590409859890693)
          ·
            refine ⟨5099231726173201848729505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27195902539590409859890693 5099231726173201848729505)
            ·
              refine ⟨3824423794629901386547129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5099231726173201848729505 3824423794629901386547129)
              ·
                refine ⟨2868317845972426039910347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3824423794629901386547129 2868317845972426039910347)
                ·
                  refine ⟨4302476768958639059865521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868317845972426039910347 4302476768958639059865521)
                  ·
                    refine ⟨3226857576718979294899141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4302476768958639059865521 3226857576718979294899141)
                    ·
                      refine ⟨605035795634808617793589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3226857576718979294899141 605035795634808617793589)
                      ·
                        rfl

theorem cell23_1178303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_1178303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178303 prefixEnd_1178303 := by exact prefixLift 1178303
  have htrace : WordTrace (prefixWord ++ tailWord_1178303) baseStart_1178303 baseEnd_1178303 := by
    simpa [prefixWord, tailWord_1178303, baseEnd_1178303] using wordTrace_append hprefix tailTrace_1178303
  have hstable : (prefixWord ++ tailWord_1178303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178303).length < 2 ^ (prefixWord ++ tailWord_1178303).sum := by decide
  have hdescent : baseEnd_1178303 < baseStart_1178303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178340 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1178340 : Nat := 118140960795 + 1178340 * 2 ^ 59
def prefixEnd_1178340 : Nat := 4983230072969 + 3 ^ 40 * 1178340 * 2
def baseEnd_1178340 : Nat := 605054794419024973030919

theorem tailTrace_1178340 : CollatzResearch.WordTrace tailWord_1178340 prefixEnd_1178340 605054794419024973030919 := by
  unfold tailWord_1178340
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488795275541449647610237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28651727034055266196813649 21488795275541449647610237)
  ·
    refine ⟨8058298228328043617853839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21488795275541449647610237 8058298228328043617853839)
    ·
      refine ⟨12087447342492065426780759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8058298228328043617853839 12087447342492065426780759)
      ·
        refine ⟨18131171013738098140171139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12087447342492065426780759 18131171013738098140171139)
        ·
          refine ⟨27196756520607147210256709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18131171013738098140171139 27196756520607147210256709)
          ·
            refine ⟨5099391847613840101923133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27196756520607147210256709 5099391847613840101923133)
            ·
              refine ⟨1912271942855190038221175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5099391847613840101923133 1912271942855190038221175)
              ·
                refine ⟨2868407914282785057331763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912271942855190038221175 2868407914282785057331763)
                ·
                  refine ⟨4302611871424177585997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868407914282785057331763 4302611871424177585997645)
                  ·
                    refine ⟨1613479451784066594749117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4302611871424177585997645 1613479451784066594749117)
                    ·
                      refine ⟨605054794419024973030919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613479451784066594749117 605054794419024973030919)
                      ·
                        rfl

theorem cell23_1178340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1178340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178340 prefixEnd_1178340 := by exact prefixLift 1178340
  have htrace : WordTrace (prefixWord ++ tailWord_1178340) baseStart_1178340 baseEnd_1178340 := by
    simpa [prefixWord, tailWord_1178340, baseEnd_1178340] using wordTrace_append hprefix tailTrace_1178340
  have hstable : (prefixWord ++ tailWord_1178340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178340).length < 2 ^ (prefixWord ++ tailWord_1178340).sum := by decide
  have hdescent : baseEnd_1178340 < baseStart_1178340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178383 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_1178383 : Nat := 118140960795 + 1178383 * 2 ^ 59
def prefixEnd_1178383 : Nat := 4983230072969 + 3 ^ 40 * 1178383 * 2
def baseEnd_1178383 : Nat := 605076874087168304793221

theorem tailTrace_1178383 : CollatzResearch.WordTrace tailWord_1178383 prefixEnd_1178383 605076874087168304793221 := by
  unfold tailWord_1178383
  simp only [CollatzResearch.WordTrace]
  refine ⟨42979158889927117639035803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28652772593284745092690535 42979158889927117639035803)
  ·
    refine ⟨64468738334890676458553705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42979158889927117639035803 64468738334890676458553705)
    ·
      refine ⟨48351553751168007343915279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64468738334890676458553705 48351553751168007343915279)
      ·
        refine ⟨72527330626752011015872919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48351553751168007343915279 72527330626752011015872919)
        ·
          refine ⟨108790995940128016523809379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72527330626752011015872919 108790995940128016523809379)
          ·
            refine ⟨163186493910192024785714069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108790995940128016523809379 163186493910192024785714069)
            ·
              refine ⟨7649366902040251161830347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163186493910192024785714069 7649366902040251161830347)
              ·
                refine ⟨11474050353060376742745521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7649366902040251161830347 11474050353060376742745521)
                ·
                  refine ⟨8605537764795282557059141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11474050353060376742745521 8605537764795282557059141)
                  ·
                    refine ⟨1613538330899115479448589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8605537764795282557059141 1613538330899115479448589)
                    ·
                      refine ⟨605076874087168304793221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613538330899115479448589 605076874087168304793221)
                      ·
                        rfl

theorem cell23_1178383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_1178383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178383 prefixEnd_1178383 := by exact prefixLift 1178383
  have htrace : WordTrace (prefixWord ++ tailWord_1178383) baseStart_1178383 baseEnd_1178383 := by
    simpa [prefixWord, tailWord_1178383, baseEnd_1178383] using wordTrace_append hprefix tailTrace_1178383
  have hstable : (prefixWord ++ tailWord_1178383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178383).length < 2 ^ (prefixWord ++ tailWord_1178383).sum := by decide
  have hdescent : baseEnd_1178383 < baseStart_1178383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178391 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_1178391 : Nat := 118140960795 + 1178391 * 2 ^ 59
def prefixEnd_1178391 : Nat := 4983230072969 + 3 ^ 40 * 1178391 * 2
def baseEnd_1178391 : Nat := 605080981932404273493185

theorem tailTrace_1178391 : CollatzResearch.WordTrace tailWord_1178391 prefixEnd_1178391 605080981932404273493185 := by
  unfold tailWord_1178391
  simp only [CollatzResearch.WordTrace]
  refine ⟨42979450673898135005327027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28652967115932090003551351 42979450673898135005327027)
  ·
    refine ⟨64469176010847202507990541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42979450673898135005327027 64469176010847202507990541)
    ·
      refine ⟨24175941004067700940496453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64469176010847202507990541 24175941004067700940496453)
      ·
        refine ⟨4532988938262693926343085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24175941004067700940496453 4532988938262693926343085)
        ·
          refine ⟨1699870851848510222378657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4532988938262693926343085 1699870851848510222378657)
          ·
            refine ⟨1274903138886382666783993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699870851848510222378657 1274903138886382666783993)
            ·
              refine ⟨956177354164787000087995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274903138886382666783993 956177354164787000087995)
              ·
                refine ⟨1434266031247180500131993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956177354164787000087995 1434266031247180500131993)
                ·
                  refine ⟨1075699523435385375098995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1434266031247180500131993 1075699523435385375098995)
                  ·
                    refine ⟨1613549285153078062648493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075699523435385375098995 1613549285153078062648493)
                    ·
                      refine ⟨605080981932404273493185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613549285153078062648493 605080981932404273493185)
                      ·
                        rfl

theorem cell23_1178391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_1178391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178391 prefixEnd_1178391 := by exact prefixLift 1178391
  have htrace : WordTrace (prefixWord ++ tailWord_1178391) baseStart_1178391 baseEnd_1178391 := by
    simpa [prefixWord, tailWord_1178391, baseEnd_1178391] using wordTrace_append hprefix tailTrace_1178391
  have hstable : (prefixWord ++ tailWord_1178391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178391).length < 2 ^ (prefixWord ++ tailWord_1178391).sum := by decide
  have hdescent : baseEnd_1178391 < baseStart_1178391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178414 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1178414 : Nat := 118140960795 + 1178414 * 2 ^ 59
def prefixEnd_1178414 : Nat := 4983230072969 + 3 ^ 40 * 1178414 * 2
def baseEnd_1178414 : Nat := 605092791987457683505579

theorem tailTrace_1178414 : CollatzResearch.WordTrace tailWord_1178414 prefixEnd_1178414 605092791987457683505579 := by
  unfold tailWord_1178414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372536194101851241676787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28653526368543206622276197 5372536194101851241676787)
  ·
    refine ⟨8058804291152776862515181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5372536194101851241676787 8058804291152776862515181)
    ·
      refine ⟨3022051609182291323443193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8058804291152776862515181 3022051609182291323443193)
      ·
        refine ⟨2266538706886718492582395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3022051609182291323443193 2266538706886718492582395)
        ·
          refine ⟨3399808060330077738873593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266538706886718492582395 3399808060330077738873593)
          ·
            refine ⟨2549856045247558304155195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399808060330077738873593 2549856045247558304155195)
            ·
              refine ⟨3824784067871337456232793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549856045247558304155195 3824784067871337456232793)
              ·
                refine ⟨2868588050903503092174595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3824784067871337456232793 2868588050903503092174595)
                ·
                  refine ⟨4302882076355254638261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868588050903503092174595 4302882076355254638261893)
                  ·
                    refine ⟨806790389316610244674105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302882076355254638261893 806790389316610244674105)
                    ·
                      refine ⟨605092791987457683505579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806790389316610244674105 605092791987457683505579)
                      ·
                        rfl

theorem cell23_1178414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1178414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178414 prefixEnd_1178414 := by exact prefixLift 1178414
  have htrace : WordTrace (prefixWord ++ tailWord_1178414) baseStart_1178414 baseEnd_1178414 := by
    simpa [prefixWord, tailWord_1178414, baseEnd_1178414] using wordTrace_append hprefix tailTrace_1178414
  have hstable : (prefixWord ++ tailWord_1178414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178414).length < 2 ^ (prefixWord ++ tailWord_1178414).sum := by decide
  have hdescent : baseEnd_1178414 < baseStart_1178414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178440 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_1178440 : Nat := 118140960795 + 1178440 * 2 ^ 59
def prefixEnd_1178440 : Nat := 4983230072969 + 3 ^ 40 * 1178440 * 2
def baseEnd_1178440 : Nat := 605106142484474581780459

theorem tailTrace_1178440 : CollatzResearch.WordTrace tailWord_1178440 prefixEnd_1178440 605106142484474581780459 := by
  unfold tailWord_1178440
  simp only [CollatzResearch.WordTrace]
  refine ⟨21490618925360308186930387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28654158567147077582573849 21490618925360308186930387)
  ·
    refine ⟨32235928388040462280395581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21490618925360308186930387 32235928388040462280395581)
    ·
      refine ⟨12088473145515173355148343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32235928388040462280395581 12088473145515173355148343)
      ·
        refine ⟨18132709718272760032722515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12088473145515173355148343 18132709718272760032722515)
        ·
          refine ⟨27199064577409140049083773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18132709718272760032722515 27199064577409140049083773)
          ·
            refine ⟨10199649216528427518406415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27199064577409140049083773 10199649216528427518406415)
            ·
              refine ⟨15299473824792641277609623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10199649216528427518406415 15299473824792641277609623)
              ·
                refine ⟨22949210737188961916414435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15299473824792641277609623 22949210737188961916414435)
                ·
                  refine ⟨34423816105783442874621653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22949210737188961916414435 34423816105783442874621653)
                  ·
                    refine ⟨806808189979299442373945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34423816105783442874621653 806808189979299442373945)
                    ·
                      refine ⟨605106142484474581780459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806808189979299442373945 605106142484474581780459)
                      ·
                        rfl

theorem cell23_1178440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_1178440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178440 prefixEnd_1178440 := by exact prefixLift 1178440
  have htrace : WordTrace (prefixWord ++ tailWord_1178440) baseStart_1178440 baseEnd_1178440 := by
    simpa [prefixWord, tailWord_1178440, baseEnd_1178440] using wordTrace_append hprefix tailTrace_1178440
  have hstable : (prefixWord ++ tailWord_1178440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178440).length < 2 ^ (prefixWord ++ tailWord_1178440).sum := by decide
  have hdescent : baseEnd_1178440 < baseStart_1178440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178467 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 2, 5]
def baseStart_1178467 : Nat := 118140960795 + 1178467 * 2 ^ 59
def prefixEnd_1178467 : Nat := 4983230072969 + 3 ^ 40 * 1178467 * 2
def baseEnd_1178467 : Nat := 201706668820715325380945

theorem tailTrace_1178467 : CollatzResearch.WordTrace tailWord_1178467 prefixEnd_1178467 201706668820715325380945 := by
  unfold tailWord_1178467
  simp only [CollatzResearch.WordTrace]
  refine ⟨42982222621622799985093655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28654815081081866656729103 42982222621622799985093655)
  ·
    refine ⟨64473333932434199977640483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42982222621622799985093655 64473333932434199977640483)
    ·
      refine ⟨96710000898651299966460725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64473333932434199977640483 96710000898651299966460725)
      ·
        refine ⟨9066562584248559371855693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96710000898651299966460725 9066562584248559371855693)
        ·
          refine ⟨3399960969093209764445885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9066562584248559371855693 3399960969093209764445885)
          ·
            refine ⟨1274985363409953661667207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3399960969093209764445885 1274985363409953661667207)
            ·
              refine ⟨1912478045114930492500811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274985363409953661667207 1912478045114930492500811)
              ·
                refine ⟨2868717067672395738751217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912478045114930492500811 2868717067672395738751217)
                ·
                  refine ⟨2151537800754296804063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868717067672395738751217 2151537800754296804063413)
                  ·
                    refine ⟨201706668820715325380945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2151537800754296804063413 201706668820715325380945)
                    ·
                      rfl

theorem cell23_1178467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 5].length) (baseStart_1178467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178467 prefixEnd_1178467 := by exact prefixLift 1178467
  have htrace : WordTrace (prefixWord ++ tailWord_1178467) baseStart_1178467 baseEnd_1178467 := by
    simpa [prefixWord, tailWord_1178467, baseEnd_1178467] using wordTrace_append hprefix tailTrace_1178467
  have hstable : (prefixWord ++ tailWord_1178467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178467).length < 2 ^ (prefixWord ++ tailWord_1178467).sum := by decide
  have hdescent : baseEnd_1178467 < baseStart_1178467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178483 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_1178483 : Nat := 118140960795 + 1178483 * 2 ^ 59
def prefixEnd_1178483 : Nat := 4983230072969 + 3 ^ 40 * 1178483 * 2
def baseEnd_1178483 : Nat := 605128222152617913542761

theorem tailTrace_1178483 : CollatzResearch.WordTrace tailWord_1178483 prefixEnd_1178483 605128222152617913542761 := by
  unfold tailWord_1178483
  simp only [CollatzResearch.WordTrace]
  refine ⟨42982806189564834717676103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28655204126376556478450735 42982806189564834717676103)
  ·
    refine ⟨64474209284347252076514155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42982806189564834717676103 64474209284347252076514155)
    ·
      refine ⟨96711313926520878114771233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64474209284347252076514155 96711313926520878114771233)
      ·
        refine ⟨72533485444890658586078425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96711313926520878114771233 72533485444890658586078425)
        ·
          refine ⟨54400114083667993939558819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72533485444890658586078425 54400114083667993939558819)
          ·
            refine ⟨81600171125501990909338229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54400114083667993939558819 81600171125501990909338229)
            ·
              refine ⟨7650016043015811647750459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81600171125501990909338229 7650016043015811647750459)
              ·
                refine ⟨11475024064523717471625689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7650016043015811647750459 11475024064523717471625689)
                ·
                  refine ⟨8606268048392788103719267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11475024064523717471625689 8606268048392788103719267)
                  ·
                    refine ⟨12909402072589182155578901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8606268048392788103719267 12909402072589182155578901)
                    ·
                      refine ⟨605128222152617913542761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12909402072589182155578901 605128222152617913542761)
                      ·
                        rfl

theorem cell23_1178483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_1178483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178483 prefixEnd_1178483 := by exact prefixLift 1178483
  have htrace : WordTrace (prefixWord ++ tailWord_1178483) baseStart_1178483 baseEnd_1178483 := by
    simpa [prefixWord, tailWord_1178483, baseEnd_1178483] using wordTrace_append hprefix tailTrace_1178483
  have hstable : (prefixWord ++ tailWord_1178483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178483).length < 2 ^ (prefixWord ++ tailWord_1178483).sum := by decide
  have hdescent : baseEnd_1178483 < baseStart_1178483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178490 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1178490 : Nat := 118140960795 + 1178490 * 2 ^ 59
def prefixEnd_1178490 : Nat := 4983230072969 + 3 ^ 40 * 1178490 * 2
def baseEnd_1178490 : Nat := 605131816517199386155229

theorem tailTrace_1178490 : CollatzResearch.WordTrace tailWord_1178490 prefixEnd_1178490 605131816517199386155229 := by
  unfold tailWord_1178490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745765375134868728295231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28655374333692983275453949 10745765375134868728295231)
  ·
    refine ⟨16118648062702303092442847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10745765375134868728295231 16118648062702303092442847)
    ·
      refine ⟨24177972094053454638664271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16118648062702303092442847 24177972094053454638664271)
      ·
        refine ⟨36266958141080181957996407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24177972094053454638664271 36266958141080181957996407)
        ·
          refine ⟨54400437211620272936994611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36266958141080181957996407 54400437211620272936994611)
          ·
            refine ⟨81600655817430409405491917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54400437211620272936994611 81600655817430409405491917)
            ·
              refine ⟨30600245931536403527059469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81600655817430409405491917 30600245931536403527059469)
              ·
                refine ⟨11475092224326151322647301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30600245931536403527059469 11475092224326151322647301)
                ·
                  refine ⟨2151579792061153372996369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11475092224326151322647301 2151579792061153372996369)
                  ·
                    refine ⟨1613684844045865029747277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2151579792061153372996369 1613684844045865029747277)
                    ·
                      refine ⟨605131816517199386155229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613684844045865029747277 605131816517199386155229)
                      ·
                        rfl

theorem cell23_1178490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1178490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178490 prefixEnd_1178490 := by exact prefixLift 1178490
  have htrace : WordTrace (prefixWord ++ tailWord_1178490) baseStart_1178490 baseEnd_1178490 := by
    simpa [prefixWord, tailWord_1178490, baseEnd_1178490] using wordTrace_append hprefix tailTrace_1178490
  have hstable : (prefixWord ++ tailWord_1178490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178490).length < 2 ^ (prefixWord ++ tailWord_1178490).sum := by decide
  have hdescent : baseEnd_1178490 < baseStart_1178490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178513 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1178513 : Nat := 118140960795 + 1178513 * 2 ^ 59
def prefixEnd_1178513 : Nat := 4983230072969 + 3 ^ 40 * 1178513 * 2
def baseEnd_1178513 : Nat := 605143626572252796167623

theorem tailTrace_1178513 : CollatzResearch.WordTrace tailWord_1178513 prefixEnd_1178513 605143626572252796167623 := by
  unfold tailWord_1178513
  simp only [CollatzResearch.WordTrace]
  refine ⟨42983900379456149841268193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28655933586304099894178795 42983900379456149841268193)
  ·
    refine ⟨32237925284592112380951145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42983900379456149841268193 32237925284592112380951145)
    ·
      refine ⟨24178443963444084285713359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32237925284592112380951145 24178443963444084285713359)
      ·
        refine ⟨36267665945166126428570039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24178443963444084285713359 36267665945166126428570039)
        ·
          refine ⟨54401498917749189642855059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36267665945166126428570039 54401498917749189642855059)
          ·
            refine ⟨81602248376623784464282589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54401498917749189642855059 81602248376623784464282589)
            ·
              refine ⟨30600843141233919174105971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81602248376623784464282589 30600843141233919174105971)
              ·
                refine ⟨45901264711850878761158957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30600843141233919174105971 45901264711850878761158957)
                ·
                  refine ⟨17212974266944079535434609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45901264711850878761158957 17212974266944079535434609)
                  ·
                    refine ⟨12909730700208059651575957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17212974266944079535434609 12909730700208059651575957)
                    ·
                      refine ⟨605143626572252796167623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12909730700208059651575957 605143626572252796167623)
                      ·
                        rfl

theorem cell23_1178513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1178513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178513 prefixEnd_1178513 := by exact prefixLift 1178513
  have htrace : WordTrace (prefixWord ++ tailWord_1178513) baseStart_1178513 baseEnd_1178513 := by
    simpa [prefixWord, tailWord_1178513, baseEnd_1178513] using wordTrace_append hprefix tailTrace_1178513
  have hstable : (prefixWord ++ tailWord_1178513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178513).length < 2 ^ (prefixWord ++ tailWord_1178513).sum := by decide
  have hdescent : baseEnd_1178513 < baseStart_1178513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178541 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1178541 : Nat := 118140960795 + 1178541 * 2 ^ 59
def prefixEnd_1178541 : Nat := 4983230072969 + 3 ^ 40 * 1178541 * 2
def baseEnd_1178541 : Nat := 605158004030578686617495

theorem tailTrace_1178541 : CollatzResearch.WordTrace tailWord_1178541 prefixEnd_1178541 605158004030578686617495 := by
  unfold tailWord_1178541
  simp only [CollatzResearch.WordTrace]
  refine ⟨42984921623354710623287477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28656614415569807082191651 42984921623354710623287477)
  ·
    refine ⟨4029836402189504120933201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42984921623354710623287477 4029836402189504120933201)
    ·
      refine ⟨3022377301642128090699901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4029836402189504120933201 3022377301642128090699901)
      ·
        refine ⟨1133391488115798034012463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3022377301642128090699901 1133391488115798034012463)
        ·
          refine ⟨1700087232173697051018695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133391488115798034012463 1700087232173697051018695)
          ·
            refine ⟨2550130848260545576528043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700087232173697051018695 2550130848260545576528043)
            ·
              refine ⟨3825196272390818364792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550130848260545576528043 3825196272390818364792065)
              ·
                refine ⟨2868897204293113773594049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825196272390818364792065 2868897204293113773594049)
                ·
                  refine ⟨2151672903219835330195537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868897204293113773594049 2151672903219835330195537)
                  ·
                    refine ⟨1613754677414876497646653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2151672903219835330195537 1613754677414876497646653)
                    ·
                      refine ⟨605158004030578686617495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613754677414876497646653 605158004030578686617495)
                      ·
                        rfl

theorem cell23_1178541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1178541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178541 prefixEnd_1178541 := by exact prefixLift 1178541
  have htrace : WordTrace (prefixWord ++ tailWord_1178541) baseStart_1178541 baseEnd_1178541 := by
    simpa [prefixWord, tailWord_1178541, baseEnd_1178541] using wordTrace_append hprefix tailTrace_1178541
  have hstable : (prefixWord ++ tailWord_1178541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178541).length < 2 ^ (prefixWord ++ tailWord_1178541).sum := by decide
  have hdescent : baseEnd_1178541 < baseStart_1178541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178570 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1178570 : Nat := 118140960795 + 1178570 * 2 ^ 59
def prefixEnd_1178570 : Nat := 4983230072969 + 3 ^ 40 * 1178570 * 2
def baseEnd_1178570 : Nat := 201724298323186357718287

theorem tailTrace_1178570 : CollatzResearch.WordTrace tailWord_1178570 prefixEnd_1178570 201724298323186357718287 := by
  unfold tailWord_1178570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746494835062412144023291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28657319560166432384062109 10746494835062412144023291)
  ·
    refine ⟨16119742252593618216034937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746494835062412144023291 16119742252593618216034937)
    ·
      refine ⟨12089806689445213662026203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16119742252593618216034937 12089806689445213662026203)
      ·
        refine ⟨18134710034167820493039305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12089806689445213662026203 18134710034167820493039305)
        ·
          refine ⟨13601032525625865369779479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18134710034167820493039305 13601032525625865369779479)
          ·
            refine ⟨20401548788438798054669219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13601032525625865369779479 20401548788438798054669219)
            ·
              refine ⟨30602323182658197082003829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20401548788438798054669219 30602323182658197082003829)
              ·
                refine ⟨2868967798374205976437859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30602323182658197082003829 2868967798374205976437859)
                ·
                  refine ⟨4303451697561308964656789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868967798374205976437859 4303451697561308964656789)
                  ·
                    refine ⟨201724298323186357718287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4303451697561308964656789 201724298323186357718287)
                    ·
                      rfl

theorem cell23_1178570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1178570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178570 prefixEnd_1178570 := by exact prefixLift 1178570
  have htrace : WordTrace (prefixWord ++ tailWord_1178570) baseStart_1178570 baseEnd_1178570 := by
    simpa [prefixWord, tailWord_1178570, baseEnd_1178570] using wordTrace_append hprefix tailTrace_1178570
  have hstable : (prefixWord ++ tailWord_1178570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178570).length < 2 ^ (prefixWord ++ tailWord_1178570).sum := by decide
  have hdescent : baseEnd_1178570 < baseStart_1178570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178574 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_1178574 : Nat := 118140960795 + 1178574 * 2 ^ 59
def prefixEnd_1178574 : Nat := 4983230072969 + 3 ^ 40 * 1178574 * 2
def baseEnd_1178574 : Nat := 201724982964059019168281

theorem tailTrace_1178574 : CollatzResearch.WordTrace tailWord_1178574 prefixEnd_1178574 201724982964059019168281 := by
  unfold tailWord_1178574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373265654029394657404847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28657416821490104839492517 5373265654029394657404847)
  ·
    refine ⟨8059898481044091986107271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5373265654029394657404847 8059898481044091986107271)
    ·
      refine ⟨12089847721566137979160907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8059898481044091986107271 12089847721566137979160907)
      ·
        refine ⟨18134771582349206968741361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12089847721566137979160907 18134771582349206968741361)
        ·
          refine ⟨13601078686761905226556021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18134771582349206968741361 13601078686761905226556021)
          ·
            refine ⟨1275101126883928614989627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13601078686761905226556021 1275101126883928614989627)
            ·
              refine ⟨1912651690325892922484441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275101126883928614989627 1912651690325892922484441)
              ·
                refine ⟨1434488767744419691863331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912651690325892922484441 1434488767744419691863331)
                ·
                  refine ⟨2151733151616629537794997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434488767744419691863331 2151733151616629537794997)
                  ·
                    refine ⟨201724982964059019168281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2151733151616629537794997 201724982964059019168281)
                    ·
                      rfl

theorem cell23_1178574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_1178574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178574 prefixEnd_1178574 := by exact prefixLift 1178574
  have htrace : WordTrace (prefixWord ++ tailWord_1178574) baseStart_1178574 baseEnd_1178574 := by
    simpa [prefixWord, tailWord_1178574, baseEnd_1178574] using wordTrace_append hprefix tailTrace_1178574
  have hstable : (prefixWord ++ tailWord_1178574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178574).length < 2 ^ (prefixWord ++ tailWord_1178574).sum := by decide
  have hdescent : baseEnd_1178574 < baseStart_1178574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178581 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1178581 : Nat := 118140960795 + 1178581 * 2 ^ 59
def prefixEnd_1178581 : Nat := 4983230072969 + 3 ^ 40 * 1178581 * 2
def baseEnd_1178581 : Nat := 605178543256758530117311

theorem tailTrace_1178581 : CollatzResearch.WordTrace tailWord_1178581 prefixEnd_1178581 605178543256758530117311 := by
  unfold tailWord_1178581
  simp only [CollatzResearch.WordTrace]
  refine ⟨42986380543209797454743597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28657587028806531636495731 42986380543209797454743597)
  ·
    refine ⟨16119892703703674045528849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42986380543209797454743597 16119892703703674045528849)
    ·
      refine ⟨12089919527777755534146637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16119892703703674045528849 12089919527777755534146637)
      ·
        refine ⟨4533719822916658325304989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12089919527777755534146637 4533719822916658325304989)
        ·
          refine ⟨1700144933593746871989371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4533719822916658325304989 1700144933593746871989371)
          ·
            refine ⟨2550217400390620307984057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700144933593746871989371 2550217400390620307984057)
            ·
              refine ⟨1912663050292965230988043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550217400390620307984057 1912663050292965230988043)
              ·
                refine ⟨2868994575439447846482065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912663050292965230988043 2868994575439447846482065)
                ·
                  refine ⟨2151745931579585884861549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868994575439447846482065 2151745931579585884861549)
                  ·
                    refine ⟨806904724342344706823081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151745931579585884861549 806904724342344706823081)
                    ·
                      refine ⟨605178543256758530117311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806904724342344706823081 605178543256758530117311)
                      ·
                        rfl

theorem cell23_1178581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1178581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178581 prefixEnd_1178581 := by exact prefixLift 1178581
  have htrace : WordTrace (prefixWord ++ tailWord_1178581) baseStart_1178581 baseEnd_1178581 := by
    simpa [prefixWord, tailWord_1178581, baseEnd_1178581] using wordTrace_append hprefix tailTrace_1178581
  have hstable : (prefixWord ++ tailWord_1178581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178581).length < 2 ^ (prefixWord ++ tailWord_1178581).sum := by decide
  have hdescent : baseEnd_1178581 < baseStart_1178581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178614 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1178614 : Nat := 118140960795 + 1178614 * 2 ^ 59
def prefixEnd_1178614 : Nat := 4983230072969 + 3 ^ 40 * 1178614 * 2
def baseEnd_1178614 : Nat := 605195488118356901004659

theorem tailTrace_1178614 : CollatzResearch.WordTrace tailWord_1178614 prefixEnd_1178614 605195488118356901004659 := by
  unfold tailWord_1178614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686724009505640255668431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28658389434726829393796597 2686724009505640255668431)
  ·
    refine ⟨4030086014258460383502647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2686724009505640255668431 4030086014258460383502647)
    ·
      refine ⟨6045129021387690575253971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030086014258460383502647 6045129021387690575253971)
      ·
        refine ⟨9067693532081535862880957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045129021387690575253971 9067693532081535862880957)
        ·
          refine ⟨3400385074530575948580359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9067693532081535862880957 3400385074530575948580359)
          ·
            refine ⟨5100577611795863922870539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400385074530575948580359 5100577611795863922870539)
            ·
              refine ⟨7650866417693795884305809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100577611795863922870539 7650866417693795884305809)
              ·
                refine ⟨5738149813270346913229357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650866417693795884305809 5738149813270346913229357)
                ·
                  refine ⟨2151806179976380092461009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5738149813270346913229357 2151806179976380092461009)
                  ·
                    refine ⟨1613854634982285069345757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2151806179976380092461009 1613854634982285069345757)
                    ·
                      refine ⟨605195488118356901004659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613854634982285069345757 605195488118356901004659)
                      ·
                        rfl

theorem cell23_1178614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1178614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178614 prefixEnd_1178614 := by exact prefixLift 1178614
  have htrace : WordTrace (prefixWord ++ tailWord_1178614) baseStart_1178614 baseEnd_1178614 := by
    simpa [prefixWord, tailWord_1178614, baseEnd_1178614] using wordTrace_append hprefix tailTrace_1178614
  have hstable : (prefixWord ++ tailWord_1178614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178614).length < 2 ^ (prefixWord ++ tailWord_1178614).sum := by decide
  have hdescent : baseEnd_1178614 < baseStart_1178614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178627 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 3]
def baseStart_1178627 : Nat := 118140960795 + 1178627 * 2 ^ 59
def prefixEnd_1178627 : Nat := 4983230072969 + 3 ^ 40 * 1178627 * 2
def baseEnd_1178627 : Nat := 605202163366865350142099

theorem tailTrace_1178627 : CollatzResearch.WordTrace tailWord_1178627 prefixEnd_1178627 605202163366865350142099 := by
  unfold tailWord_1178627
  simp only [CollatzResearch.WordTrace]
  refine ⟨42988058301043147310918135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28658705534028764873945423 42988058301043147310918135)
  ·
    refine ⟨64482087451564720966377203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42988058301043147310918135 64482087451564720966377203)
    ·
      refine ⟨96723131177347081449565805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64482087451564720966377203 96723131177347081449565805)
      ·
        refine ⟨36271174191505155543587177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96723131177347081449565805 36271174191505155543587177)
        ·
          refine ⟨27203380643628866657690383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36271174191505155543587177 27203380643628866657690383)
          ·
            refine ⟨40805070965443299986535575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27203380643628866657690383 40805070965443299986535575)
            ·
              refine ⟨61207606448164949979803363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40805070965443299986535575 61207606448164949979803363)
              ·
                refine ⟨91811409672247424969705045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61207606448164949979803363 91811409672247424969705045)
                ·
                  refine ⟨1075914957096649511363731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 91811409672247424969705045 1075914957096649511363731)
                  ·
                    refine ⟨1613872435644974267045597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075914957096649511363731 1613872435644974267045597)
                    ·
                      refine ⟨605202163366865350142099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1613872435644974267045597 605202163366865350142099)
                      ·
                        rfl

theorem cell23_1178627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_1178627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178627 prefixEnd_1178627 := by exact prefixLift 1178627
  have htrace : WordTrace (prefixWord ++ tailWord_1178627) baseStart_1178627 baseEnd_1178627 := by
    simpa [prefixWord, tailWord_1178627, baseEnd_1178627] using wordTrace_append hprefix tailTrace_1178627
  have hstable : (prefixWord ++ tailWord_1178627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178627).length < 2 ^ (prefixWord ++ tailWord_1178627).sum := by decide
  have hdescent : baseEnd_1178627 < baseStart_1178627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178642 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1178642 : Nat := 118140960795 + 1178642 * 2 ^ 59
def prefixEnd_1178642 : Nat := 4983230072969 + 3 ^ 40 * 1178642 * 2
def baseEnd_1178642 : Nat := 201736621858894263818177

theorem tailTrace_1178642 : CollatzResearch.WordTrace tailWord_1178642 prefixEnd_1178642 201736621858894263818177 := by
  unfold tailWord_1178642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10747151348997201218178545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28659070263992536581809453 10747151348997201218178545)
  ·
    refine ⟨8060363511747900913633909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10747151348997201218178545 8060363511747900913633909)
    ·
      refine ⟨755659079226365710653179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8060363511747900913633909 755659079226365710653179)
      ·
        refine ⟨1133488618839548565979769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755659079226365710653179 1133488618839548565979769)
        ·
          refine ⟨850116464129661424484827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133488618839548565979769 850116464129661424484827)
          ·
            refine ⟨1275174696194492136727241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850116464129661424484827 1275174696194492136727241)
            ·
              refine ⟨956381022145869102545431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275174696194492136727241 956381022145869102545431)
              ·
                refine ⟨1434571533218803653818147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956381022145869102545431 1434571533218803653818147)
                ·
                  refine ⟨2151857299828205480727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434571533218803653818147 2151857299828205480727221)
                  ·
                    refine ⟨201736621858894263818177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2151857299828205480727221 201736621858894263818177)
                    ·
                      rfl

theorem cell23_1178642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1178642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178642 prefixEnd_1178642 := by exact prefixLift 1178642
  have htrace : WordTrace (prefixWord ++ tailWord_1178642) baseStart_1178642 baseEnd_1178642 := by
    simpa [prefixWord, tailWord_1178642, baseEnd_1178642] using wordTrace_append hprefix tailTrace_1178642
  have hstable : (prefixWord ++ tailWord_1178642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178642).length < 2 ^ (prefixWord ++ tailWord_1178642).sum := by decide
  have hdescent : baseEnd_1178642 < baseStart_1178642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178777 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_1178777 : Nat := 118140960795 + 1178777 * 2 ^ 59
def prefixEnd_1178777 : Nat := 4983230072969 + 3 ^ 40 * 1178777 * 2
def baseEnd_1178777 : Nat := 605279185465039763266409

theorem tailTrace_1178777 : CollatzResearch.WordTrace tailWord_1178777 prefixEnd_1178777 605279185465039763266409 := by
  unfold tailWord_1178777
  simp only [CollatzResearch.WordTrace]
  refine ⟨42993529250499722928878585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28662352833666481952585723 42993529250499722928878585)
  ·
    refine ⟨32245146937874792196658939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42993529250499722928878585 32245146937874792196658939)
    ·
      refine ⟨48367720406812188294988409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32245146937874792196658939 48367720406812188294988409)
      ·
        refine ⟨36275790305109141221241307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48367720406812188294988409 36275790305109141221241307)
        ·
          refine ⟨54413685457663711831861961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36275790305109141221241307 54413685457663711831861961)
          ·
            refine ⟨40810264093247783873896471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54413685457663711831861961 40810264093247783873896471)
            ·
              refine ⟨61215396139871675810844707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40810264093247783873896471 61215396139871675810844707)
              ·
                refine ⟨91823094209807513716267061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61215396139871675810844707 91823094209807513716267061)
                ·
                  refine ⟨8608415082169454410900037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91823094209807513716267061 8608415082169454410900037)
                  ·
                    refine ⟨1614077827906772702043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8608415082169454410900037 1614077827906772702043757)
                    ·
                      refine ⟨605279185465039763266409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614077827906772702043757 605279185465039763266409)
                      ·
                        rfl

theorem cell23_1178777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_1178777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178777 prefixEnd_1178777 := by exact prefixLift 1178777
  have htrace : WordTrace (prefixWord ++ tailWord_1178777) baseStart_1178777 baseEnd_1178777 := by
    simpa [prefixWord, tailWord_1178777, baseEnd_1178777] using wordTrace_append hprefix tailTrace_1178777
  have hstable : (prefixWord ++ tailWord_1178777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178777).length < 2 ^ (prefixWord ++ tailWord_1178777).sum := by decide
  have hdescent : baseEnd_1178777 < baseStart_1178777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178784 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 3, 4]
def baseStart_1178784 : Nat := 118140960795 + 1178784 * 2 ^ 59
def prefixEnd_1178784 : Nat := 4983230072969 + 3 ^ 40 * 1178784 * 2
def baseEnd_1178784 : Nat := 201760926609873745292959

theorem tailTrace_1178784 : CollatzResearch.WordTrace tailWord_1178784 prefixEnd_1178784 201760926609873745292959 := by
  unfold tailWord_1178784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496892280737181562191703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28662523040982908749588937 21496892280737181562191703)
  ·
    refine ⟨32245338421105772343287555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21496892280737181562191703 32245338421105772343287555)
    ·
      refine ⟨48368007631658658514931333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32245338421105772343287555 48368007631658658514931333)
      ·
        refine ⟨9069001430935998471549625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48368007631658658514931333 9069001430935998471549625)
        ·
          refine ⟨6801751073201998853662219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9069001430935998471549625 6801751073201998853662219)
          ·
            refine ⟨10202626609802998280493329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801751073201998853662219 10202626609802998280493329)
            ·
              refine ⟨7651969957352248710369997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10202626609802998280493329 7651969957352248710369997)
              ·
                refine ⟨2869488734007093266388749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7651969957352248710369997 2869488734007093266388749)
                ·
                  refine ⟨1076058275252659974895781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2869488734007093266388749 1076058275252659974895781)
                  ·
                    refine ⟨201760926609873745292959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076058275252659974895781 201760926609873745292959)
                    ·
                      rfl

theorem cell23_1178784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_1178784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178784 prefixEnd_1178784 := by exact prefixLift 1178784
  have htrace : WordTrace (prefixWord ++ tailWord_1178784) baseStart_1178784 baseEnd_1178784 := by
    simpa [prefixWord, tailWord_1178784, baseEnd_1178784] using wordTrace_append hprefix tailTrace_1178784
  have hstable : (prefixWord ++ tailWord_1178784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178784).length < 2 ^ (prefixWord ++ tailWord_1178784).sum := by decide
  have hdescent : baseEnd_1178784 < baseStart_1178784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178791 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_1178791 : Nat := 118140960795 + 1178791 * 2 ^ 59
def prefixEnd_1178791 : Nat := 4983230072969 + 3 ^ 40 * 1178791 * 2
def baseEnd_1178791 : Nat := 605286374194202708491345

theorem tailTrace_1178791 : CollatzResearch.WordTrace tailWord_1178791 prefixEnd_1178791 605286374194202708491345 := by
  unfold tailWord_1178791
  simp only [CollatzResearch.WordTrace]
  refine ⟨42994039872449003319888227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28662693248299335546592151 42994039872449003319888227)
  ·
    refine ⟨64491059808673504979832341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42994039872449003319888227 64491059808673504979832341)
    ·
      refine ⟨3023018428531570545929641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64491059808673504979832341 3023018428531570545929641)
      ·
        refine ⟨2267263821398677909447231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023018428531570545929641 2267263821398677909447231)
        ·
          refine ⟨3400895732098016864170847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267263821398677909447231 3400895732098016864170847)
          ·
            refine ⟨5101343598147025296256271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400895732098016864170847 5101343598147025296256271)
            ·
              refine ⟨7652015397220537944384407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101343598147025296256271 7652015397220537944384407)
              ·
                refine ⟨11478023095830806916576611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7652015397220537944384407 11478023095830806916576611)
                ·
                  refine ⟨17217034643746210374864917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11478023095830806916576611 17217034643746210374864917)
                  ·
                    refine ⟨807048498925603611321793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17217034643746210374864917 807048498925603611321793)
                    ·
                      refine ⟨605286374194202708491345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807048498925603611321793 605286374194202708491345)
                      ·
                        rfl

theorem cell23_1178791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_1178791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178791 prefixEnd_1178791 := by exact prefixLift 1178791
  have htrace : WordTrace (prefixWord ++ tailWord_1178791) baseStart_1178791 baseEnd_1178791 := by
    simpa [prefixWord, tailWord_1178791, baseEnd_1178791] using wordTrace_append hprefix tailTrace_1178791
  have hstable : (prefixWord ++ tailWord_1178791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178791).length < 2 ^ (prefixWord ++ tailWord_1178791).sum := by decide
  have hdescent : baseEnd_1178791 < baseStart_1178791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178801 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_1178801 : Nat := 118140960795 + 1178801 * 2 ^ 59
def prefixEnd_1178801 : Nat := 4983230072969 + 3 ^ 40 * 1178801 * 2
def baseEnd_1178801 : Nat := 201763836333582556455433

theorem tailTrace_1178801 : CollatzResearch.WordTrace tailWord_1178801 prefixEnd_1178801 201763836333582556455433 := by
  unfold tailWord_1178801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42994404602412775027752257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28662936401608516685168171 42994404602412775027752257)
  ·
    refine ⟨32245803451809581270814193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42994404602412775027752257 32245803451809581270814193)
    ·
      refine ⟨24184352588857185953110645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32245803451809581270814193 24184352588857185953110645)
      ·
        refine ⟨2267283055205361183104123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24184352588857185953110645 2267283055205361183104123)
        ·
          refine ⟨3400924582808041774656185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267283055205361183104123 3400924582808041774656185)
          ·
            refine ⟨2550693437106031330992139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400924582808041774656185 2550693437106031330992139)
            ·
              refine ⟨3826040155659046996488209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550693437106031330992139 3826040155659046996488209)
              ·
                refine ⟨2869530116744285247366157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826040155659046996488209 2869530116744285247366157)
                ·
                  refine ⟨1076073793779106967762309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2869530116744285247366157 1076073793779106967762309)
                  ·
                    refine ⟨201763836333582556455433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076073793779106967762309 201763836333582556455433)
                    ·
                      rfl

theorem cell23_1178801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_1178801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178801 prefixEnd_1178801 := by exact prefixLift 1178801
  have htrace : WordTrace (prefixWord ++ tailWord_1178801) baseStart_1178801 baseEnd_1178801 := by
    simpa [prefixWord, tailWord_1178801, baseEnd_1178801] using wordTrace_append hprefix tailTrace_1178801
  have hstable : (prefixWord ++ tailWord_1178801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178801).length < 2 ^ (prefixWord ++ tailWord_1178801).sum := by decide
  have hdescent : baseEnd_1178801 < baseStart_1178801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178827 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 5, 5]
def baseStart_1178827 : Nat := 118140960795 + 1178827 * 2 ^ 59
def prefixEnd_1178827 : Nat := 4983230072969 + 3 ^ 40 * 1178827 * 2
def baseEnd_1178827 : Nat := 201768286499254855880393

theorem tailTrace_1178827 : CollatzResearch.WordTrace tailWord_1178827 prefixEnd_1178827 201768286499254855880393 := by
  unfold tailWord_1178827
  simp only [CollatzResearch.WordTrace]
  refine ⟨42995352900318581468198735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28663568600212387645465823 42995352900318581468198735)
  ·
    refine ⟨64493029350477872202298103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42995352900318581468198735 64493029350477872202298103)
    ·
      refine ⟨96739544025716808303447155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64493029350477872202298103 96739544025716808303447155)
      ·
        refine ⟨145109316038575212455170733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96739544025716808303447155 145109316038575212455170733)
        ·
          refine ⟨54415993514465704670689025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145109316038575212455170733 54415993514465704670689025)
          ·
            refine ⟨40811995135849278503016769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54415993514465704670689025 40811995135849278503016769)
            ·
              refine ⟨30608996351886958877262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40811995135849278503016769 30608996351886958877262577)
              ·
                refine ⟨22956747263915219157946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30608996351886958877262577 22956747263915219157946933)
                ·
                  refine ⟨2152195055992051796057525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22956747263915219157946933 2152195055992051796057525)
                  ·
                    refine ⟨201768286499254855880393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2152195055992051796057525 201768286499254855880393)
                    ·
                      rfl

theorem cell23_1178827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].length) (baseStart_1178827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178827 prefixEnd_1178827 := by exact prefixLift 1178827
  have htrace : WordTrace (prefixWord ++ tailWord_1178827) baseStart_1178827 baseEnd_1178827 := by
    simpa [prefixWord, tailWord_1178827, baseEnd_1178827] using wordTrace_append hprefix tailTrace_1178827
  have hstable : (prefixWord ++ tailWord_1178827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178827).length < 2 ^ (prefixWord ++ tailWord_1178827).sum := by decide
  have hdescent : baseEnd_1178827 < baseStart_1178827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178861 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1178861 : Nat := 118140960795 + 1178861 * 2 ^ 59
def prefixEnd_1178861 : Nat := 4983230072969 + 3 ^ 40 * 1178861 * 2
def baseEnd_1178861 : Nat := 201774105946672478205341

theorem tailTrace_1178861 : CollatzResearch.WordTrace tailWord_1178861 prefixEnd_1178861 201774105946672478205341 := by
  unfold tailWord_1178861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42996592982195405274936437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28664395321463603516624291 42996592982195405274936437)
  ·
    refine ⟨4030930592080819244525291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42996592982195405274936437 4030930592080819244525291)
    ·
      refine ⟨6046395888121228866787937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030930592080819244525291 6046395888121228866787937)
      ·
        refine ⟨4534796916090921650090953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6046395888121228866787937 4534796916090921650090953)
        ·
          refine ⟨3401097687068191237568215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534796916090921650090953 3401097687068191237568215)
          ·
            refine ⟨5101646530602286856352323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401097687068191237568215 5101646530602286856352323)
            ·
              refine ⟨7652469795903430284528485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101646530602286856352323 7652469795903430284528485)
              ·
                refine ⟨1434838086731893178349091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7652469795903430284528485 1434838086731893178349091)
                ·
                  refine ⟨2152257130097839767523637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434838086731893178349091 2152257130097839767523637)
                  ·
                    refine ⟨201774105946672478205341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2152257130097839767523637 201774105946672478205341)
                    ·
                      rfl

theorem cell23_1178861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1178861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178861 prefixEnd_1178861 := by exact prefixLift 1178861
  have htrace : WordTrace (prefixWord ++ tailWord_1178861) baseStart_1178861 baseEnd_1178861 := by
    simpa [prefixWord, tailWord_1178861, baseEnd_1178861] using wordTrace_append hprefix tailTrace_1178861
  have hstable : (prefixWord ++ tailWord_1178861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178861).length < 2 ^ (prefixWord ++ tailWord_1178861).sum := by decide
  have hdescent : baseEnd_1178861 < baseStart_1178861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178874 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_1178874 : Nat := 118140960795 + 1178874 * 2 ^ 59
def prefixEnd_1178874 : Nat := 4983230072969 + 3 ^ 40 * 1178874 * 2
def baseEnd_1178874 : Nat := 201776331029508627917821

theorem tailTrace_1178874 : CollatzResearch.WordTrace tailWord_1178874 prefixEnd_1178874 201776331029508627917821 := by
  unfold tailWord_1178874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749266782787077123789919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28664711420765538996773117 10749266782787077123789919)
  ·
    refine ⟨16123900174180615685684879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10749266782787077123789919 16123900174180615685684879)
    ·
      refine ⟨24185850261270923528527319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16123900174180615685684879 24185850261270923528527319)
      ·
        refine ⟨36278775391906385292790979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24185850261270923528527319 36278775391906385292790979)
        ·
          refine ⟨54418163087859577939186469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36278775391906385292790979 54418163087859577939186469)
          ·
            refine ⟨10203405578973670863597463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54418163087859577939186469 10203405578973670863597463)
            ·
              refine ⟨15305108368460506295396195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10203405578973670863597463 15305108368460506295396195)
              ·
                refine ⟨22957662552690759443094293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15305108368460506295396195 22957662552690759443094293)
                ·
                  refine ⟨1076140432157379348895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22957662552690759443094293 1076140432157379348895045)
                  ·
                    refine ⟨201776331029508627917821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076140432157379348895045 201776331029508627917821)
                    ·
                      rfl

theorem cell23_1178874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_1178874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178874 prefixEnd_1178874 := by exact prefixLift 1178874
  have htrace : WordTrace (prefixWord ++ tailWord_1178874) baseStart_1178874 baseEnd_1178874 := by
    simpa [prefixWord, tailWord_1178874, baseEnd_1178874] using wordTrace_append hprefix tailTrace_1178874
  have hstable : (prefixWord ++ tailWord_1178874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178874).length < 2 ^ (prefixWord ++ tailWord_1178874).sum := by decide
  have hdescent : baseEnd_1178874 < baseStart_1178874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178881 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1178881 : Nat := 118140960795 + 1178881 * 2 ^ 59
def prefixEnd_1178881 : Nat := 4983230072969 + 3 ^ 40 * 1178881 * 2
def baseEnd_1178881 : Nat := 605332587453107356365931

theorem tailTrace_1178881 : CollatzResearch.WordTrace tailWord_1178881 prefixEnd_1178881 605332587453107356365931 := by
  unfold tailWord_1178881
  simp only [CollatzResearch.WordTrace]
  refine ⟨42997322442122948690664497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28664881628081965793776331 42997322442122948690664497)
  ·
    refine ⟨32247991831592211517998373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42997322442122948690664497 32247991831592211517998373)
    ·
      refine ⟨6046498468423539659624695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32247991831592211517998373 6046498468423539659624695)
      ·
        refine ⟨9069747702635309489437043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046498468423539659624695 9069747702635309489437043)
        ·
          refine ⟨13604621553952964234155565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069747702635309489437043 13604621553952964234155565)
          ·
            refine ⟨5101733082732361587808337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13604621553952964234155565 5101733082732361587808337)
            ·
              refine ⟨3826299812049271190856253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5101733082732361587808337 3826299812049271190856253)
              ·
                refine ⟨1434862429518476696571095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3826299812049271190856253 1434862429518476696571095)
                ·
                  refine ⟨2152293644277715044856643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434862429518476696571095 2152293644277715044856643)
                  ·
                    refine ⟨3228440466416572567284965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152293644277715044856643 3228440466416572567284965)
                    ·
                      refine ⟨605332587453107356365931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3228440466416572567284965 605332587453107356365931)
                      ·
                        rfl

theorem cell23_1178881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1178881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178881 prefixEnd_1178881 := by exact prefixLift 1178881
  have htrace : WordTrace (prefixWord ++ tailWord_1178881) baseStart_1178881 baseEnd_1178881 := by
    simpa [prefixWord, tailWord_1178881, baseEnd_1178881] using wordTrace_append hprefix tailTrace_1178881
  have hstable : (prefixWord ++ tailWord_1178881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178881).length < 2 ^ (prefixWord ++ tailWord_1178881).sum := by decide
  have hdescent : baseEnd_1178881 < baseStart_1178881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178894 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1178894 : Nat := 118140960795 + 1178894 * 2 ^ 59
def prefixEnd_1178894 : Nat := 4983230072969 + 3 ^ 40 * 1178894 * 2
def baseEnd_1178894 : Nat := 605339262701615805503371

theorem tailTrace_1178894 : CollatzResearch.WordTrace tailWord_1178894 prefixEnd_1178894 605339262701615805503371 := by
  unfold tailWord_1178894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374724573884481488860967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28665197727383901273925157 5374724573884481488860967)
  ·
    refine ⟨8062086860826722233291451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5374724573884481488860967 8062086860826722233291451)
    ·
      refine ⟨12093130291240083349937177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062086860826722233291451 12093130291240083349937177)
      ·
        refine ⟨9069847718430062512452883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12093130291240083349937177 9069847718430062512452883)
        ·
          refine ⟨13604771577645093768679325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069847718430062512452883 13604771577645093768679325)
          ·
            refine ⟨5101789341616910163254747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13604771577645093768679325 5101789341616910163254747)
            ·
              refine ⟨7652684012425365244882121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101789341616910163254747 7652684012425365244882121)
              ·
                refine ⟨5739513009319023933661591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7652684012425365244882121 5739513009319023933661591)
                ·
                  refine ⟨8609269513978535900492387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5739513009319023933661591 8609269513978535900492387)
                  ·
                    refine ⟨12913904270967803850738581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8609269513978535900492387 12913904270967803850738581)
                    ·
                      refine ⟨605339262701615805503371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12913904270967803850738581 605339262701615805503371)
                      ·
                        rfl

theorem cell23_1178894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1178894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178894 prefixEnd_1178894 := by exact prefixLift 1178894
  have htrace : WordTrace (prefixWord ++ tailWord_1178894) baseStart_1178894 baseEnd_1178894 := by
    simpa [prefixWord, tailWord_1178894, baseEnd_1178894] using wordTrace_append hprefix tailTrace_1178894
  have hstable : (prefixWord ++ tailWord_1178894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178894).length < 2 ^ (prefixWord ++ tailWord_1178894).sum := by decide
  have hdescent : baseEnd_1178894 < baseStart_1178894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178904 : List Nat := [2, 1, 2, 3, 1, 4, 2, 8]
def baseStart_1178904 : Nat := 118140960795 + 1178904 * 2 ^ 59
def prefixEnd_1178904 : Nat := 4983230072969 + 3 ^ 40 * 1178904 * 2
def baseEnd_1178904 : Nat := 22420162870672620976975

theorem tailTrace_1178904 : CollatzResearch.WordTrace tailWord_1178904 prefixEnd_1178904 22420162870672620976975 := by
  unfold tailWord_1178904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499080660519811809375883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28665440880693082412501177 21499080660519811809375883)
  ·
    refine ⟨32248620990779717714063825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21499080660519811809375883 32248620990779717714063825)
    ·
      refine ⟨24186465743084788285547869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32248620990779717714063825 24186465743084788285547869)
      ·
        refine ⟨9069924653656795607080451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24186465743084788285547869 9069924653656795607080451)
        ·
          refine ⟨13604886980485193410620677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069924653656795607080451 13604886980485193410620677)
          ·
            refine ⟨2550916308840973764491377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13604886980485193410620677 2550916308840973764491377)
            ·
              refine ⟨1913187231630730323368533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550916308840973764491377 1913187231630730323368533)
              ·
                refine ⟨22420162870672620976975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1913187231630730323368533 22420162870672620976975)
                ·
                  rfl

theorem cell23_1178904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 8].length) (baseStart_1178904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178904 prefixEnd_1178904 := by exact prefixLift 1178904
  have htrace : WordTrace (prefixWord ++ tailWord_1178904) baseStart_1178904 baseEnd_1178904 := by
    simpa [prefixWord, tailWord_1178904, baseEnd_1178904] using wordTrace_append hprefix tailTrace_1178904
  have hstable : (prefixWord ++ tailWord_1178904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178904).length < 2 ^ (prefixWord ++ tailWord_1178904).sum := by decide
  have hdescent : baseEnd_1178904 < baseStart_1178904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178907 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_1178907 : Nat := 118140960795 + 1178907 * 2 ^ 59
def prefixEnd_1178907 : Nat := 4983230072969 + 3 ^ 40 * 1178907 * 2
def baseEnd_1178907 : Nat := 605345937950124254640811

theorem tailTrace_1178907 : CollatzResearch.WordTrace tailWord_1178907 prefixEnd_1178907 605345937950124254640811 := by
  unfold tailWord_1178907
  simp only [CollatzResearch.WordTrace]
  refine ⟨42998270740028755131110975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28665513826685836754073983 42998270740028755131110975)
  ·
    refine ⟨64497406110043132696666463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42998270740028755131110975 64497406110043132696666463)
    ·
      refine ⟨96746109165064699044999695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64497406110043132696666463 96746109165064699044999695)
      ·
        refine ⟨145119163747597048567499543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96746109165064699044999695 145119163747597048567499543)
        ·
          refine ⟨217678745621395572851249315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145119163747597048567499543 217678745621395572851249315)
          ·
            refine ⟨326518118432093359276873973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217678745621395572851249315 326518118432093359276873973)
            ·
              refine ⟨30611073603008752432206935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326518118432093359276873973 30611073603008752432206935)
              ·
                refine ⟨45916610404513128648310403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30611073603008752432206935 45916610404513128648310403)
                ·
                  refine ⟨68874915606769692972465605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45916610404513128648310403 68874915606769692972465605)
                  ·
                    refine ⟨12914046676269317432337301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68874915606769692972465605 12914046676269317432337301)
                    ·
                      refine ⟨605345937950124254640811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12914046676269317432337301 605345937950124254640811)
                      ·
                        rfl

theorem cell23_1178907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_1178907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178907 prefixEnd_1178907 := by exact prefixLift 1178907
  have htrace : WordTrace (prefixWord ++ tailWord_1178907) baseStart_1178907 baseEnd_1178907 := by
    simpa [prefixWord, tailWord_1178907, baseEnd_1178907] using wordTrace_append hprefix tailTrace_1178907
  have hstable : (prefixWord ++ tailWord_1178907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178907).length < 2 ^ (prefixWord ++ tailWord_1178907).sum := by decide
  have hdescent : baseEnd_1178907 < baseStart_1178907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178908 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1178908 : Nat := 118140960795 + 1178908 * 2 ^ 59
def prefixEnd_1178908 : Nat := 4983230072969 + 3 ^ 40 * 1178908 * 2
def baseEnd_1178908 : Nat := 201782150476926250242769

theorem tailTrace_1178908 : CollatzResearch.WordTrace tailWord_1178908 prefixEnd_1178908 201782150476926250242769 := by
  unfold tailWord_1178908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499153606512566150948689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28665538142016754867931585 21499153606512566150948689)
  ·
    refine ⟨16124365204884424613211517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21499153606512566150948689 16124365204884424613211517)
    ·
      refine ⟨6046636951831659229954319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16124365204884424613211517 6046636951831659229954319)
      ·
        refine ⟨9069955427747488844931479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046636951831659229954319 9069955427747488844931479)
        ·
          refine ⟨13604933141621233267397219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9069955427747488844931479 13604933141621233267397219)
          ·
            refine ⟨20407399712431849901095829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604933141621233267397219 20407399712431849901095829)
            ·
              refine ⟨956596861520242964113867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20407399712431849901095829 956596861520242964113867)
              ·
                refine ⟨1434895292280364446170801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956596861520242964113867 1434895292280364446170801)
                ·
                  refine ⟨1076171469210273334628101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1434895292280364446170801 1076171469210273334628101)
                  ·
                    refine ⟨201782150476926250242769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076171469210273334628101 201782150476926250242769)
                    ·
                      rfl

theorem cell23_1178908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1178908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178908 prefixEnd_1178908 := by exact prefixLift 1178908
  have htrace : WordTrace (prefixWord ++ tailWord_1178908) baseStart_1178908 baseEnd_1178908 := by
    simpa [prefixWord, tailWord_1178908, baseEnd_1178908] using wordTrace_append hprefix tailTrace_1178908
  have hstable : (prefixWord ++ tailWord_1178908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178908).length < 2 ^ (prefixWord ++ tailWord_1178908).sum := by decide
  have hdescent : baseEnd_1178908 < baseStart_1178908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178931 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3]
def baseStart_1178931 : Nat := 118140960795 + 1178931 * 2 ^ 59
def prefixEnd_1178931 : Nat := 4983230072969 + 3 ^ 40 * 1178931 * 2
def baseEnd_1178931 : Nat := 605358261485832160740701

theorem tailTrace_1178931 : CollatzResearch.WordTrace tailWord_1178931 prefixEnd_1178931 605358261485832160740701 := by
  unfold tailWord_1178931
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999146091941807229984647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28666097394627871486656431 42999146091941807229984647)
  ·
    refine ⟨64498719137912710844976971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42999146091941807229984647 64498719137912710844976971)
    ·
      refine ⟨96748078706869066267465457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64498719137912710844976971 96748078706869066267465457)
      ·
        refine ⟨72561059030151799700599093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96748078706869066267465457 72561059030151799700599093)
        ·
          refine ⟨6802599284076731221931165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72561059030151799700599093 6802599284076731221931165)
          ·
            refine ⟨2550974731528774208224187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6802599284076731221931165 2550974731528774208224187)
            ·
              refine ⟨3826462097293161312336281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550974731528774208224187 3826462097293161312336281)
              ·
                refine ⟨2869846572969870984252211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826462097293161312336281 2869846572969870984252211)
                ·
                  refine ⟨4304769859454806476378317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869846572969870984252211 4304769859454806476378317)
                  ·
                    refine ⟨1614288697295552428641869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4304769859454806476378317 1614288697295552428641869)
                    ·
                      refine ⟨605358261485832160740701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614288697295552428641869 605358261485832160740701)
                      ·
                        rfl

theorem cell23_1178931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_1178931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178931 prefixEnd_1178931 := by exact prefixLift 1178931
  have htrace : WordTrace (prefixWord ++ tailWord_1178931) baseStart_1178931 baseEnd_1178931 := by
    simpa [prefixWord, tailWord_1178931, baseEnd_1178931] using wordTrace_append hprefix tailTrace_1178931
  have hstable : (prefixWord ++ tailWord_1178931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178931).length < 2 ^ (prefixWord ++ tailWord_1178931).sum := by decide
  have hdescent : baseEnd_1178931 < baseStart_1178931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178932 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1178932 : Nat := 118140960795 + 1178932 * 2 ^ 59
def prefixEnd_1178932 : Nat := 4983230072969 + 3 ^ 40 * 1178932 * 2
def baseEnd_1178932 : Nat := 605358774966486656828197

theorem tailTrace_1178932 : CollatzResearch.WordTrace tailWord_1178932 prefixEnd_1178932 605358774966486656828197 := by
  unfold tailWord_1178932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499591282469092200385525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28666121709958789600514033 21499591282469092200385525)
  ·
    refine ⟨2015586682731477393786143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21499591282469092200385525 2015586682731477393786143)
    ·
      refine ⟨3023380024097216090679215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015586682731477393786143 3023380024097216090679215)
      ·
        refine ⟨4535070036145824136018823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023380024097216090679215 4535070036145824136018823)
        ·
          refine ⟨6802605054218736204028235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535070036145824136018823 6802605054218736204028235)
          ·
            refine ⟨10203907581328104306042353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6802605054218736204028235 10203907581328104306042353)
            ·
              refine ⟨7652930685996078229531765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10203907581328104306042353 7652930685996078229531765)
              ·
                refine ⟨717462251812132334018603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7652930685996078229531765 717462251812132334018603)
                ·
                  refine ⟨1076193377718198501027905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717462251812132334018603 1076193377718198501027905)
                  ·
                    refine ⟨807145033288648875770929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076193377718198501027905 807145033288648875770929)
                    ·
                      refine ⟨605358774966486656828197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807145033288648875770929 605358774966486656828197)
                      ·
                        rfl

theorem cell23_1178932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1178932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178932 prefixEnd_1178932 := by exact prefixLift 1178932
  have htrace : WordTrace (prefixWord ++ tailWord_1178932) baseStart_1178932 baseEnd_1178932 := by
    simpa [prefixWord, tailWord_1178932, baseEnd_1178932] using wordTrace_append hprefix tailTrace_1178932
  have hstable : (prefixWord ++ tailWord_1178932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178932).length < 2 ^ (prefixWord ++ tailWord_1178932).sum := by decide
  have hdescent : baseEnd_1178932 < baseStart_1178932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178966 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1178966 : Nat := 118140960795 + 1178966 * 2 ^ 59
def prefixEnd_1178966 : Nat := 4983230072969 + 3 ^ 40 * 1178966 * 2
def baseEnd_1178966 : Nat := 605376233308739523803041

theorem tailTrace_1178966 : CollatzResearch.WordTrace tailWord_1178966 prefixEnd_1178966 605376233308739523803041 := by
  unfold tailWord_1178966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687526415425938012969297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28666948431210005471672501 2687526415425938012969297)
  ·
    refine ⟨2015644811569453509726973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2687526415425938012969297 2015644811569453509726973)
    ·
      refine ⟨755866804338545066147615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2015644811569453509726973 755866804338545066147615)
      ·
        refine ⟨1133800206507817599221423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755866804338545066147615 1133800206507817599221423)
        ·
          refine ⟨1700700309761726398832135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133800206507817599221423 1700700309761726398832135)
          ·
            refine ⟨2551050464642589598248203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700700309761726398832135 2551050464642589598248203)
            ·
              refine ⟨3826575696963884397372305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551050464642589598248203 3826575696963884397372305)
              ·
                refine ⟨2869931772722913298029229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826575696963884397372305 2869931772722913298029229)
                ·
                  refine ⟨1076224414771092486760961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2869931772722913298029229 1076224414771092486760961)
                  ·
                    refine ⟨807168311078319365070721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076224414771092486760961 807168311078319365070721)
                    ·
                      refine ⟨605376233308739523803041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807168311078319365070721 605376233308739523803041)
                      ·
                        rfl

theorem cell23_1178966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1178966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178966 prefixEnd_1178966 := by exact prefixLift 1178966
  have htrace : WordTrace (prefixWord ++ tailWord_1178966) baseStart_1178966 baseEnd_1178966 := by
    simpa [prefixWord, tailWord_1178966, baseEnd_1178966] using wordTrace_append hprefix tailTrace_1178966
  have hstable : (prefixWord ++ tailWord_1178966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178966).length < 2 ^ (prefixWord ++ tailWord_1178966).sum := by decide
  have hdescent : baseEnd_1178966 < baseStart_1178966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178988 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_1178988 : Nat := 118140960795 + 1178988 * 2 ^ 59
def prefixEnd_1178988 : Nat := 4983230072969 + 3 ^ 40 * 1178988 * 2
def baseEnd_1178988 : Nat := 605387529883138437727939

theorem tailTrace_1178988 : CollatzResearch.WordTrace tailWord_1178988 prefixEnd_1178988 605387529883138437727939 := by
  unfold tailWord_1178988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21500612526367652982404809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28667483368490203976539745 21500612526367652982404809)
  ·
    refine ⟨16125459394775739736803607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21500612526367652982404809 16125459394775739736803607)
    ·
      refine ⟨24188189092163609605205411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16125459394775739736803607 24188189092163609605205411)
      ·
        refine ⟨36282283638245414407808117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24188189092163609605205411 36282283638245414407808117)
        ·
          refine ⟨3401464091085507600732011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36282283638245414407808117 3401464091085507600732011)
          ·
            refine ⟨5102196136628261401098017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401464091085507600732011 5102196136628261401098017)
            ·
              refine ⟨3826647102471196050823513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102196136628261401098017 3826647102471196050823513)
              ·
                refine ⟨2869985326853397038117635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826647102471196050823513 2869985326853397038117635)
                ·
                  refine ⟨4304977990280095557176453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869985326853397038117635 4304977990280095557176453)
                  ·
                    refine ⟨807183373177517916970585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304977990280095557176453 807183373177517916970585)
                    ·
                      refine ⟨605387529883138437727939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807183373177517916970585 605387529883138437727939)
                      ·
                        rfl

theorem cell23_1178988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_1178988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178988 prefixEnd_1178988 := by exact prefixLift 1178988
  have htrace : WordTrace (prefixWord ++ tailWord_1178988) baseStart_1178988 baseEnd_1178988 := by
    simpa [prefixWord, tailWord_1178988, baseEnd_1178988] using wordTrace_append hprefix tailTrace_1178988
  have hstable : (prefixWord ++ tailWord_1178988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178988).length < 2 ^ (prefixWord ++ tailWord_1178988).sum := by decide
  have hdescent : baseEnd_1178988 < baseStart_1178988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178994 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_1178994 : Nat := 118140960795 + 1178994 * 2 ^ 59
def prefixEnd_1178994 : Nat := 4983230072969 + 3 ^ 40 * 1178994 * 2
def baseEnd_1178994 : Nat := 67265623418562823805879

theorem tailTrace_1178994 : CollatzResearch.WordTrace tailWord_1178994 prefixEnd_1178994 67265623418562823805879 := by
  unfold tailWord_1178994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10750360972678392247382009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28667629260475712659685357 10750360972678392247382009)
  ·
    refine ⟨8062770729508794185536507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10750360972678392247382009 8062770729508794185536507)
    ·
      refine ⟨12094156094263191278304761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062770729508794185536507 12094156094263191278304761)
      ·
        refine ⟨9070617070697393458728571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12094156094263191278304761 9070617070697393458728571)
        ·
          refine ⟨13605925606046090188092857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9070617070697393458728571 13605925606046090188092857)
          ·
            refine ⟨10204444204534567641069643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13605925606046090188092857 10204444204534567641069643)
            ·
              refine ⟨15306666306801851461604465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10204444204534567641069643 15306666306801851461604465)
              ·
                refine ⟨11479999730101388596203349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15306666306801851461604465 11479999730101388596203349)
                ·
                  refine ⟨67265623418562823805879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11479999730101388596203349 67265623418562823805879)
                  ·
                    rfl

theorem cell23_1178994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_1178994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1178994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1178994 prefixEnd_1178994 := by exact prefixLift 1178994
  have htrace : WordTrace (prefixWord ++ tailWord_1178994) baseStart_1178994 baseEnd_1178994 := by
    simpa [prefixWord, tailWord_1178994, baseEnd_1178994] using wordTrace_append hprefix tailTrace_1178994
  have hstable : (prefixWord ++ tailWord_1178994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178994).length < 2 ^ (prefixWord ++ tailWord_1178994).sum := by decide
  have hdescent : baseEnd_1178994 < baseStart_1178994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179011 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 7]
def baseStart_1179011 : Nat := 118140960795 + 1179011 * 2 ^ 59
def prefixEnd_1179011 : Nat := 4983230072969 + 3 ^ 40 * 1179011 * 2
def baseEnd_1179011 : Nat := 67266593326465760860037

theorem tailTrace_1179011 : CollatzResearch.WordTrace tailWord_1179011 prefixEnd_1179011 67266593326465760860037 := by
  unfold tailWord_1179011
  simp only [CollatzResearch.WordTrace]
  refine ⟨43002063931651980892896887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28668042621101320595264591 43002063931651980892896887)
  ·
    refine ⟨64503095897477971339345331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43002063931651980892896887 64503095897477971339345331)
    ·
      refine ⟨96754643846216957009017997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64503095897477971339345331 96754643846216957009017997)
      ·
        refine ⟨36282991442331358878381749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96754643846216957009017997 36282991442331358878381749)
        ·
          refine ⟨3401530447718564894848289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36282991442331358878381749 3401530447718564894848289)
          ·
            refine ⟨2551147835788923671136217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3401530447718564894848289 2551147835788923671136217)
            ·
              refine ⟨1913360876841692753352163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551147835788923671136217 1913360876841692753352163)
              ·
                refine ⟨2870041315262539130028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913360876841692753352163 2870041315262539130028245)
                ·
                  refine ⟨67266593326465760860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2870041315262539130028245 67266593326465760860037)
                  ·
                    rfl

theorem cell23_1179011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 7].length) (baseStart_1179011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179011 prefixEnd_1179011 := by exact prefixLift 1179011
  have htrace : WordTrace (prefixWord ++ tailWord_1179011) baseStart_1179011 baseEnd_1179011 := by
    simpa [prefixWord, tailWord_1179011, baseEnd_1179011] using wordTrace_append hprefix tailTrace_1179011
  have hstable : (prefixWord ++ tailWord_1179011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179011).length < 2 ^ (prefixWord ++ tailWord_1179011).sum := by decide
  have hdescent : baseEnd_1179011 < baseStart_1179011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179022 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1179022 : Nat := 118140960795 + 1179022 * 2 ^ 59
def prefixEnd_1179022 : Nat := 4983230072969 + 3 ^ 40 * 1179022 * 2
def baseEnd_1179022 : Nat := 605404988225391304702783

theorem tailTrace_1179022 : CollatzResearch.WordTrace tailWord_1179022 prefixEnd_1179022 605404988225391304702783 := by
  unfold tailWord_1179022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375308141826516221443415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28668310089741419847698213 5375308141826516221443415)
  ·
    refine ⟨8062962212739774332165123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375308141826516221443415 8062962212739774332165123)
    ·
      refine ⟨12094443319109661498247685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062962212739774332165123 12094443319109661498247685)
      ·
        refine ⟨2267708122333061530921441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12094443319109661498247685 2267708122333061530921441)
        ·
          refine ⟨1700781091749796148191081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267708122333061530921441 1700781091749796148191081)
          ·
            refine ⟨1275585818812347111143311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700781091749796148191081 1275585818812347111143311)
            ·
              refine ⟨1913378728218520666714967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275585818812347111143311 1913378728218520666714967)
              ·
                refine ⟨2870068092327781000072451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913378728218520666714967 2870068092327781000072451)
                ·
                  refine ⟨4305102138491671500108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870068092327781000072451 4305102138491671500108677)
                  ·
                    refine ⟨807206650967188406270377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305102138491671500108677 807206650967188406270377)
                    ·
                      refine ⟨605404988225391304702783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807206650967188406270377 605404988225391304702783)
                      ·
                        rfl

theorem cell23_1179022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1179022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179022 prefixEnd_1179022 := by exact prefixLift 1179022
  have htrace : WordTrace (prefixWord ++ tailWord_1179022) baseStart_1179022 baseEnd_1179022 := by
    simpa [prefixWord, tailWord_1179022, baseEnd_1179022] using wordTrace_append hprefix tailTrace_1179022
  have hstable : (prefixWord ++ tailWord_1179022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179022).length < 2 ^ (prefixWord ++ tailWord_1179022).sum := by decide
  have hdescent : baseEnd_1179022 < baseStart_1179022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179068 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1179068 : Nat := 118140960795 + 1179068 * 2 ^ 59
def prefixEnd_1179068 : Nat := 4983230072969 + 3 ^ 40 * 1179068 * 2
def baseEnd_1179068 : Nat := 605428608335498124727571

theorem tailTrace_1179068 : CollatzResearch.WordTrace tailWord_1179068 prefixEnd_1179068 605428608335498124727571 := by
  unfold tailWord_1179068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21502071446222739813860929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28669428594963653085147905 21502071446222739813860929)
  ·
    refine ⟨16126553584667054860395697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21502071446222739813860929 16126553584667054860395697)
    ·
      refine ⟨12094915188500291145296773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16126553584667054860395697 12094915188500291145296773)
      ·
        refine ⟨2267796597843804589743145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12094915188500291145296773 2267796597843804589743145)
        ·
          refine ⟨1700847448382853442307359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267796597843804589743145 1700847448382853442307359)
          ·
            refine ⟨2551271172574280163461039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700847448382853442307359 2551271172574280163461039)
            ·
              refine ⟨3826906758861420245191559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551271172574280163461039 3826906758861420245191559)
              ·
                refine ⟨5740360138292130367787339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826906758861420245191559 5740360138292130367787339)
                ·
                  refine ⟨8610540207438195551681009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5740360138292130367787339 8610540207438195551681009)
                  ·
                    refine ⟨6457905155578646663760757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8610540207438195551681009 6457905155578646663760757)
                    ·
                      refine ⟨605428608335498124727571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6457905155578646663760757 605428608335498124727571)
                      ·
                        rfl

theorem cell23_1179068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1179068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179068 prefixEnd_1179068 := by exact prefixLift 1179068
  have htrace : WordTrace (prefixWord ++ tailWord_1179068) baseStart_1179068 baseEnd_1179068 := by
    simpa [prefixWord, tailWord_1179068, baseEnd_1179068] using wordTrace_append hprefix tailTrace_1179068
  have hstable : (prefixWord ++ tailWord_1179068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179068).length < 2 ^ (prefixWord ++ tailWord_1179068).sum := by decide
  have hdescent : baseEnd_1179068 < baseStart_1179068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179081 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_1179081 : Nat := 118140960795 + 1179081 * 2 ^ 59
def prefixEnd_1179081 : Nat := 4983230072969 + 3 ^ 40 * 1179081 * 2
def baseEnd_1179081 : Nat := 605435283584006573865011

theorem tailTrace_1179081 : CollatzResearch.WordTrace tailWord_1179081 prefixEnd_1179081 605435283584006573865011 := by
  unfold tailWord_1179081
  simp only [CollatzResearch.WordTrace]
  refine ⟨43004617041398382847945097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28669744694265588565296731 43004617041398382847945097)
  ·
    refine ⟨32253462781048787135958823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43004617041398382847945097 32253462781048787135958823)
    ·
      refine ⟨48380194171573180703938235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32253462781048787135958823 48380194171573180703938235)
      ·
        refine ⟨72570291257359771055907353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48380194171573180703938235 72570291257359771055907353)
        ·
          refine ⟨54427718443019828291930515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72570291257359771055907353 54427718443019828291930515)
          ·
            refine ⟨81641577664529742437895773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54427718443019828291930515 81641577664529742437895773)
            ·
              refine ⟨30615591624198653414210915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81641577664529742437895773 30615591624198653414210915)
              ·
                refine ⟨45923387436297980121316373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30615591624198653414210915 45923387436297980121316373)
                ·
                  refine ⟨2152658786076467818186705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45923387436297980121316373 2152658786076467818186705)
                  ·
                    refine ⟨1614494089557350863640029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152658786076467818186705 1614494089557350863640029)
                    ·
                      refine ⟨605435283584006573865011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614494089557350863640029 605435283584006573865011)
                      ·
                        rfl

theorem cell23_1179081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_1179081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179081 prefixEnd_1179081 := by exact prefixLift 1179081
  have htrace : WordTrace (prefixWord ++ tailWord_1179081) baseStart_1179081 baseEnd_1179081 := by
    simpa [prefixWord, tailWord_1179081, baseEnd_1179081] using wordTrace_append hprefix tailTrace_1179081
  have hstable : (prefixWord ++ tailWord_1179081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179081).length < 2 ^ (prefixWord ++ tailWord_1179081).sum := by decide
  have hdescent : baseEnd_1179081 < baseStart_1179081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179098 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1179098 : Nat := 118140960795 + 1179098 * 2 ^ 59
def prefixEnd_1179098 : Nat := 4983230072969 + 3 ^ 40 * 1179098 * 2
def baseEnd_1179098 : Nat := 605444012755133007352433

theorem tailTrace_1179098 : CollatzResearch.WordTrace tailWord_1179098 prefixEnd_1179098 605444012755133007352433 := by
  unfold tailWord_1179098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751309270584198687828487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28670158054891196500875965 10751309270584198687828487)
  ·
    refine ⟨16126963905876298031742731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751309270584198687828487 16126963905876298031742731)
    ·
      refine ⟨24190445858814447047614097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16126963905876298031742731 24190445858814447047614097)
      ·
        refine ⟨18142834394110835285710573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24190445858814447047614097 18142834394110835285710573)
        ·
          refine ⟨6803562897791563232141465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18142834394110835285710573 6803562897791563232141465)
          ·
            refine ⟨5102672173343672424106099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6803562897791563232141465 5102672173343672424106099)
            ·
              refine ⟨7654008260015508636159149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102672173343672424106099 7654008260015508636159149)
              ·
                refine ⟨2870253097505815738559681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7654008260015508636159149 2870253097505815738559681)
                ·
                  refine ⟨2152689823129361803919761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870253097505815738559681 2152689823129361803919761)
                  ·
                    refine ⟨1614517367347021352939821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152689823129361803919761 1614517367347021352939821)
                    ·
                      refine ⟨605444012755133007352433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614517367347021352939821 605444012755133007352433)
                      ·
                        rfl

theorem cell23_1179098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1179098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179098 prefixEnd_1179098 := by exact prefixLift 1179098
  have htrace : WordTrace (prefixWord ++ tailWord_1179098) baseStart_1179098 baseEnd_1179098 := by
    simpa [prefixWord, tailWord_1179098, baseEnd_1179098] using wordTrace_append hprefix tailTrace_1179098
  have hstable : (prefixWord ++ tailWord_1179098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179098).length < 2 ^ (prefixWord ++ tailWord_1179098).sum := by decide
  have hdescent : baseEnd_1179098 < baseStart_1179098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179118 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_1179118 : Nat := 118140960795 + 1179118 * 2 ^ 59
def prefixEnd_1179118 : Nat := 4983230072969 + 3 ^ 40 * 1179118 * 2
def baseEnd_1179118 : Nat := 67272698040913658789149

theorem tailTrace_1179118 : CollatzResearch.WordTrace tailWord_1179118 prefixEnd_1179118 67272698040913658789149 := by
  unfold tailWord_1179118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375745817783042270880251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28670644361509558778028005 5375745817783042270880251)
  ·
    refine ⟨8063618726674563406320377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375745817783042270880251 8063618726674563406320377)
    ·
      refine ⟨6047714045005922554740283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8063618726674563406320377 6047714045005922554740283)
      ·
        refine ⟨9071571067508883832110425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6047714045005922554740283 9071571067508883832110425)
        ·
          refine ⟨6803678300631662874082819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9071571067508883832110425 6803678300631662874082819)
          ·
            refine ⟨10205517450947494311124229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6803678300631662874082819 10205517450947494311124229)
            ·
              refine ⟨1913534522052655183335793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10205517450947494311124229 1913534522052655183335793)
              ·
                refine ⟨1435150891539491387501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913534522052655183335793 1435150891539491387501845)
                ·
                  refine ⟨67272698040913658789149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1435150891539491387501845 67272698040913658789149)
                  ·
                    rfl

theorem cell23_1179118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_1179118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179118 prefixEnd_1179118 := by exact prefixLift 1179118
  have htrace : WordTrace (prefixWord ++ tailWord_1179118) baseStart_1179118 baseEnd_1179118 := by
    simpa [prefixWord, tailWord_1179118, baseEnd_1179118] using wordTrace_append hprefix tailTrace_1179118
  have hstable : (prefixWord ++ tailWord_1179118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179118).length < 2 ^ (prefixWord ++ tailWord_1179118).sum := by decide
  have hdescent : baseEnd_1179118 < baseStart_1179118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179122 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_1179122 : Nat := 118140960795 + 1179122 * 2 ^ 59
def prefixEnd_1179122 : Nat := 4983230072969 + 3 ^ 40 * 1179122 * 2
def baseEnd_1179122 : Nat := 201818778763613637817441

theorem tailTrace_1179122 : CollatzResearch.WordTrace tailWord_1179122 prefixEnd_1179122 201818778763613637817441 := by
  unfold tailWord_1179122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751528108562461712546905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28670741622833231233458413 10751528108562461712546905)
  ·
    refine ⟨8063646081421846284410179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10751528108562461712546905 8063646081421846284410179)
    ·
      refine ⟨12095469122132769426615269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8063646081421846284410179 12095469122132769426615269)
      ·
        refine ⟨2267900460399894267490363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12095469122132769426615269 2267900460399894267490363)
        ·
          refine ⟨3401850690599841401235545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267900460399894267490363 3401850690599841401235545)
          ·
            refine ⟨2551388017949881050926659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3401850690599841401235545 2551388017949881050926659)
            ·
              refine ⟨3827082026924821576389989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551388017949881050926659 3827082026924821576389989)
              ·
                refine ⟨717577880048404045573123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3827082026924821576389989 717577880048404045573123)
                ·
                  refine ⟨1076366820072606068359685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717577880048404045573123 1076366820072606068359685)
                  ·
                    refine ⟨201818778763613637817441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076366820072606068359685 201818778763613637817441)
                    ·
                      rfl

theorem cell23_1179122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_1179122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179122 prefixEnd_1179122 := by exact prefixLift 1179122
  have htrace : WordTrace (prefixWord ++ tailWord_1179122) baseStart_1179122 baseEnd_1179122 := by
    simpa [prefixWord, tailWord_1179122, baseEnd_1179122] using wordTrace_append hprefix tailTrace_1179122
  have hstable : (prefixWord ++ tailWord_1179122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179122).length < 2 ^ (prefixWord ++ tailWord_1179122).sum := by decide
  have hdescent : baseEnd_1179122 < baseStart_1179122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179151 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_1179151 : Nat := 118140960795 + 1179151 * 2 ^ 59
def prefixEnd_1179151 : Nat := 4983230072969 + 3 ^ 40 * 1179151 * 2
def baseEnd_1179151 : Nat := 605471227229821299989689

theorem tailTrace_1179151 : CollatzResearch.WordTrace tailWord_1179151 prefixEnd_1179151 605471227229821299989689 := by
  unfold tailWord_1179151
  simp only [CollatzResearch.WordTrace]
  refine ⟨43007170151144784802993307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28671446767429856535328871 43007170151144784802993307)
  ·
    refine ⟨64510755226717177204489961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43007170151144784802993307 64510755226717177204489961)
    ·
      refine ⟨48383066420037882903367471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64510755226717177204489961 48383066420037882903367471)
      ·
        refine ⟨72574599630056824355051207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48383066420037882903367471 72574599630056824355051207)
        ·
          refine ⟨108861899445085236532576811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72574599630056824355051207 108861899445085236532576811)
          ·
            refine ⟨163292849167627854798865217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108861899445085236532576811 163292849167627854798865217)
            ·
              refine ⟨122469636875720891099148913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163292849167627854798865217 122469636875720891099148913)
              ·
                refine ⟨91852227656790668324361685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122469636875720891099148913 91852227656790668324361685)
                ·
                  refine ⟨2152786585706031288852227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91852227656790668324361685 2152786585706031288852227)
                  ·
                    refine ⟨3229179878559046933278341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2152786585706031288852227 3229179878559046933278341)
                    ·
                      refine ⟨605471227229821299989689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3229179878559046933278341 605471227229821299989689)
                      ·
                        rfl

theorem cell23_1179151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_1179151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179151 prefixEnd_1179151 := by exact prefixLift 1179151
  have htrace : WordTrace (prefixWord ++ tailWord_1179151) baseStart_1179151 baseEnd_1179151 := by
    simpa [prefixWord, tailWord_1179151, baseEnd_1179151] using wordTrace_append hprefix tailTrace_1179151
  have hstable : (prefixWord ++ tailWord_1179151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179151).length < 2 ^ (prefixWord ++ tailWord_1179151).sum := by decide
  have hdescent : baseEnd_1179151 < baseStart_1179151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179155 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 2, 3, 2]
def baseStart_1179155 : Nat := 118140960795 + 1179155 * 2 ^ 59
def prefixEnd_1179155 : Nat := 4983230072969 + 3 ^ 40 * 1179155 * 2
def baseEnd_1179155 : Nat := 605473281152439284339671

theorem tailTrace_1179155 : CollatzResearch.WordTrace tailWord_1179155 prefixEnd_1179155 605473281152439284339671 := by
  unfold tailWord_1179155
  simp only [CollatzResearch.WordTrace]
  refine ⟨43007316043130293486138919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28671544028753528990759279 43007316043130293486138919)
  ·
    refine ⟨64510974064695440229208379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43007316043130293486138919 64510974064695440229208379)
    ·
      refine ⟨96766461097043160343812569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64510974064695440229208379 96766461097043160343812569)
      ·
        refine ⟨72574845822782370257859427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96766461097043160343812569 72574845822782370257859427)
        ·
          refine ⟨108862268734173555386789141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72574845822782370257859427 108862268734173555386789141)
          ·
            refine ⟨5102918846914385408755741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108862268734173555386789141 5102918846914385408755741)
            ·
              refine ⟨1913594567592894528283403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5102918846914385408755741 1913594567592894528283403)
              ·
                refine ⟨2870391851389341792425105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913594567592894528283403 2870391851389341792425105)
                ·
                  refine ⟨2152793888542006344318829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870391851389341792425105 2152793888542006344318829)
                  ·
                    refine ⟨807297708203252379119561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152793888542006344318829 807297708203252379119561)
                    ·
                      refine ⟨605473281152439284339671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807297708203252379119561 605473281152439284339671)
                      ·
                        rfl

theorem cell23_1179155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 3, 2].length) (baseStart_1179155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179155 prefixEnd_1179155 := by exact prefixLift 1179155
  have htrace : WordTrace (prefixWord ++ tailWord_1179155) baseStart_1179155 baseEnd_1179155 := by
    simpa [prefixWord, tailWord_1179155, baseEnd_1179155] using wordTrace_append hprefix tailTrace_1179155
  have hstable : (prefixWord ++ tailWord_1179155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179155).length < 2 ^ (prefixWord ++ tailWord_1179155).sum := by decide
  have hdescent : baseEnd_1179155 < baseStart_1179155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179205 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_1179205 : Nat := 118140960795 + 1179205 * 2 ^ 59
def prefixEnd_1179205 : Nat := 4983230072969 + 3 ^ 40 * 1179205 * 2
def baseEnd_1179205 : Nat := 605498955185164088714441

theorem tailTrace_1179205 : CollatzResearch.WordTrace tailWord_1179205 prefixEnd_1179205 605498955185164088714441 := by
  unfold tailWord_1179205
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009139692949152025459069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28672759795299434683639379 43009139692949152025459069)
  ·
    refine ⟨16128427384855932009547151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43009139692949152025459069 16128427384855932009547151)
    ·
      refine ⟨24192641077283898014320727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16128427384855932009547151 24192641077283898014320727)
      ·
        refine ⟨36288961615925847021481091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24192641077283898014320727 36288961615925847021481091)
        ·
          refine ⟨54433442423888770532221637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36288961615925847021481091 54433442423888770532221637)
          ·
            refine ⟨10206270454479144474791557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54433442423888770532221637 10206270454479144474791557)
            ·
              refine ⟨1913675710214839589023417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10206270454479144474791557 1913675710214839589023417)
              ·
                refine ⟨1435256782661129691767563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913675710214839589023417 1435256782661129691767563)
                ·
                  refine ⟨2152885173991694537651345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435256782661129691767563 2152885173991694537651345)
                  ·
                    refine ⟨1614663880493770903238509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2152885173991694537651345 1614663880493770903238509)
                    ·
                      refine ⟨605498955185164088714441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614663880493770903238509 605498955185164088714441)
                      ·
                        rfl

theorem cell23_1179205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_1179205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179205 prefixEnd_1179205 := by exact prefixLift 1179205
  have htrace : WordTrace (prefixWord ++ tailWord_1179205) baseStart_1179205 baseEnd_1179205 := by
    simpa [prefixWord, tailWord_1179205, baseEnd_1179205] using wordTrace_append hprefix tailTrace_1179205
  have hstable : (prefixWord ++ tailWord_1179205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179205).length < 2 ^ (prefixWord ++ tailWord_1179205).sum := by decide
  have hdescent : baseEnd_1179205 < baseStart_1179205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179213 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1179213 : Nat := 118140960795 + 1179213 * 2 ^ 59
def prefixEnd_1179213 : Nat := 4983230072969 + 3 ^ 40 * 1179213 * 2
def baseEnd_1179213 : Nat := 605503063030400057414405

theorem tailTrace_1179213 : CollatzResearch.WordTrace tailWord_1179213 prefixEnd_1179213 605503063030400057414405 := by
  unfold tailWord_1179213
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009431476920169391750293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28672954317946779594500195 43009431476920169391750293)
  ·
    refine ⟨2016067100480632940238295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43009431476920169391750293 2016067100480632940238295)
    ·
      refine ⟨3024100650720949410357443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016067100480632940238295 3024100650720949410357443)
      ·
        refine ⟨4536150976081424115536165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024100650720949410357443 4536150976081424115536165)
        ·
          refine ⟨850528308015267021663031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4536150976081424115536165 850528308015267021663031)
          ·
            refine ⟨1275792462022900532494547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850528308015267021663031 1275792462022900532494547)
            ·
              refine ⟨1913688693034350798741821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275792462022900532494547 1913688693034350798741821)
              ·
                refine ⟨717633259887881549528183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913688693034350798741821 717633259887881549528183)
                ·
                  refine ⟨1076449889831822324292275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717633259887881549528183 1076449889831822324292275)
                  ·
                    refine ⟨1614674834747733486438413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1076449889831822324292275 1614674834747733486438413)
                    ·
                      refine ⟨605503063030400057414405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614674834747733486438413 605503063030400057414405)
                      ·
                        rfl

theorem cell23_1179213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1179213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179213 prefixEnd_1179213 := by exact prefixLift 1179213
  have htrace : WordTrace (prefixWord ++ tailWord_1179213) baseStart_1179213 baseEnd_1179213 := by
    simpa [prefixWord, tailWord_1179213, baseEnd_1179213] using wordTrace_append hprefix tailTrace_1179213
  have hstable : (prefixWord ++ tailWord_1179213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179213).length < 2 ^ (prefixWord ++ tailWord_1179213).sum := by decide
  have hdescent : baseEnd_1179213 < baseStart_1179213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179221 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1179221 : Nat := 118140960795 + 1179221 * 2 ^ 59
def prefixEnd_1179221 : Nat := 4983230072969 + 3 ^ 40 * 1179221 * 2
def baseEnd_1179221 : Nat := 201835723625212008704789

theorem tailTrace_1179221 : CollatzResearch.WordTrace tailWord_1179221 prefixEnd_1179221 201835723625212008704789 := by
  unfold tailWord_1179221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009723260891186758041517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28673148840594124505361011 43009723260891186758041517)
  ·
    refine ⟨16128646222834195034265569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43009723260891186758041517 16128646222834195034265569)
    ·
      refine ⟨12096484667125646275699177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16128646222834195034265569 12096484667125646275699177)
      ·
        refine ⟨9072363500344234706774383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12096484667125646275699177 9072363500344234706774383)
        ·
          refine ⟨13608545250516352060161575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072363500344234706774383 13608545250516352060161575)
          ·
            refine ⟨20412817875774528090242363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608545250516352060161575 20412817875774528090242363)
            ·
              refine ⟨30619226813661792135363545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20412817875774528090242363 30619226813661792135363545)
              ·
                refine ⟨22964420110246344101522659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30619226813661792135363545 22964420110246344101522659)
                ·
                  refine ⟨34446630165369516152283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22964420110246344101522659 34446630165369516152283989)
                  ·
                    refine ⟨201835723625212008704789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 34446630165369516152283989 201835723625212008704789)
                    ·
                      rfl

theorem cell23_1179221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1179221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179221 prefixEnd_1179221 := by exact prefixLift 1179221
  have htrace : WordTrace (prefixWord ++ tailWord_1179221) baseStart_1179221 baseEnd_1179221 := by
    simpa [prefixWord, tailWord_1179221, baseEnd_1179221] using wordTrace_append hprefix tailTrace_1179221
  have hstable : (prefixWord ++ tailWord_1179221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179221).length < 2 ^ (prefixWord ++ tailWord_1179221).sum := by decide
  have hdescent : baseEnd_1179221 < baseStart_1179221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179235 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1179235 : Nat := 118140960795 + 1179235 * 2 ^ 59
def prefixEnd_1179235 : Nat := 4983230072969 + 3 ^ 40 * 1179235 * 2
def baseEnd_1179235 : Nat := 605514359604798971339303

theorem tailTrace_1179235 : CollatzResearch.WordTrace tailWord_1179235 prefixEnd_1179235 605514359604798971339303 := by
  unfold tailWord_1179235
  simp only [CollatzResearch.WordTrace]
  refine ⟨43010233882840467149051159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28673489255226978099367439 43010233882840467149051159)
  ·
    refine ⟨64515350824260700723576739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43010233882840467149051159 64515350824260700723576739)
    ·
      refine ⟨96773026236391051085365109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64515350824260700723576739 96773026236391051085365109)
      ·
        refine ⟨9072471209661661039252979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96773026236391051085365109 9072471209661661039252979)
        ·
          refine ⟨13608706814492491558879469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072471209661661039252979 13608706814492491558879469)
          ·
            refine ⟨5103265055434684334579801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13608706814492491558879469 5103265055434684334579801)
            ·
              refine ⟨3827448791576013250934851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5103265055434684334579801 3827448791576013250934851)
              ·
                refine ⟨5741173187364019876402277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827448791576013250934851 5741173187364019876402277)
                ·
                  refine ⟨1076469972630753726825427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5741173187364019876402277 1076469972630753726825427)
                  ·
                    refine ⟨1614704958946130590238141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1076469972630753726825427 1614704958946130590238141)
                    ·
                      refine ⟨605514359604798971339303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614704958946130590238141 605514359604798971339303)
                      ·
                        rfl

theorem cell23_1179235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1179235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179235 prefixEnd_1179235 := by exact prefixLift 1179235
  have htrace : WordTrace (prefixWord ++ tailWord_1179235) baseStart_1179235 baseEnd_1179235 := by
    simpa [prefixWord, tailWord_1179235, baseEnd_1179235] using wordTrace_append hprefix tailTrace_1179235
  have hstable : (prefixWord ++ tailWord_1179235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179235).length < 2 ^ (prefixWord ++ tailWord_1179235).sum := by decide
  have hdescent : baseEnd_1179235 < baseStart_1179235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179236 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_1179236 : Nat := 118140960795 + 1179236 * 2 ^ 59
def prefixEnd_1179236 : Nat := 4983230072969 + 3 ^ 40 * 1179236 * 2
def baseEnd_1179236 : Nat := 605514873085453467426799

theorem tailTrace_1179236 : CollatzResearch.WordTrace tailWord_1179236 prefixEnd_1179236 605514873085453467426799 := by
  unfold tailWord_1179236
  simp only [CollatzResearch.WordTrace]
  refine ⟨21505135177918422159918781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28673513570557896213225041 21505135177918422159918781)
  ·
    refine ⟨8064425691719408309969543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21505135177918422159918781 8064425691719408309969543)
    ·
      refine ⟨12096638537579112464954315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8064425691719408309969543 12096638537579112464954315)
      ·
        refine ⟨18144957806368668697431473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12096638537579112464954315 18144957806368668697431473)
        ·
          refine ⟨13608718354776501523073605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18144957806368668697431473 13608718354776501523073605)
          ·
            refine ⟨2551634691520594035576301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13608718354776501523073605 2551634691520594035576301)
            ·
              refine ⟨956863009320222763341113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551634691520594035576301 956863009320222763341113)
              ·
                refine ⟨717647256990167072505835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956863009320222763341113 717647256990167072505835)
                ·
                  refine ⟨1076470885485250608758753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717647256990167072505835 1076470885485250608758753)
                  ·
                    refine ⟨807353164113937956569065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076470885485250608758753 807353164113937956569065)
                    ·
                      refine ⟨605514873085453467426799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807353164113937956569065 605514873085453467426799)
                      ·
                        rfl

theorem cell23_1179236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_1179236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179236 prefixEnd_1179236 := by exact prefixLift 1179236
  have htrace : WordTrace (prefixWord ++ tailWord_1179236) baseStart_1179236 baseEnd_1179236 := by
    simpa [prefixWord, tailWord_1179236, baseEnd_1179236] using wordTrace_append hprefix tailTrace_1179236
  have hstable : (prefixWord ++ tailWord_1179236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179236).length < 2 ^ (prefixWord ++ tailWord_1179236).sum := by decide
  have hdescent : baseEnd_1179236 < baseStart_1179236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179246 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1179246 : Nat := 118140960795 + 1179246 * 2 ^ 59
def prefixEnd_1179246 : Nat := 4983230072969 + 3 ^ 40 * 1179246 * 2
def baseEnd_1179246 : Nat := 201840002630666142767251

theorem tailTrace_1179246 : CollatzResearch.WordTrace tailWord_1179246 prefixEnd_1179246 201840002630666142767251 := by
  unfold tailWord_1179246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376329385725077003462699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28673756723867077351801061 5376329385725077003462699)
  ·
    refine ⟨8064494078587615505194049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5376329385725077003462699 8064494078587615505194049)
    ·
      refine ⟨6048370558940711628895537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8064494078587615505194049 6048370558940711628895537)
      ·
        refine ⟨4536277919205533721671653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6048370558940711628895537 4536277919205533721671653)
        ·
          refine ⟨850552109851037572813435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4536277919205533721671653 850552109851037572813435)
          ·
            refine ⟨1275828164776556359220153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850552109851037572813435 1275828164776556359220153)
            ·
              refine ⟨956871123582417269415115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275828164776556359220153 956871123582417269415115)
              ·
                refine ⟨1435306685373625904122673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956871123582417269415115 1435306685373625904122673)
                ·
                  refine ⟨1076480014030219428092005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435306685373625904122673 1076480014030219428092005)
                  ·
                    refine ⟨201840002630666142767251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076480014030219428092005 201840002630666142767251)
                    ·
                      rfl

theorem cell23_1179246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1179246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179246 prefixEnd_1179246 := by exact prefixLift 1179246
  have htrace : WordTrace (prefixWord ++ tailWord_1179246) baseStart_1179246 baseEnd_1179246 := by
    simpa [prefixWord, tailWord_1179246, baseEnd_1179246] using wordTrace_append hprefix tailTrace_1179246
  have hstable : (prefixWord ++ tailWord_1179246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179246).length < 2 ^ (prefixWord ++ tailWord_1179246).sum := by decide
  have hdescent : baseEnd_1179246 < baseStart_1179246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179251 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 6]
def baseStart_1179251 : Nat := 118140960795 + 1179251 * 2 ^ 59
def prefixEnd_1179251 : Nat := 4983230072969 + 3 ^ 40 * 1179251 * 2
def baseEnd_1179251 : Nat := 201840858431756969579743

theorem tailTrace_1179251 : CollatzResearch.WordTrace tailWord_1179251 prefixEnd_1179251 201840858431756969579743 := by
  unfold tailWord_1179251
  simp only [CollatzResearch.WordTrace]
  refine ⟨43010817450782501881633607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28673878300521667921089071 43010817450782501881633607)
  ·
    refine ⟨64516226176173752822450411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43010817450782501881633607 64516226176173752822450411)
    ·
      refine ⟨96774339264260629233675617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64516226176173752822450411 96774339264260629233675617)
      ·
        refine ⟨72580754448195471925256713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96774339264260629233675617 72580754448195471925256713)
        ·
          refine ⟨54435565836146603943942535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72580754448195471925256713 54435565836146603943942535)
          ·
            refine ⟨81653348754219905915913803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54435565836146603943942535 81653348754219905915913803)
            ·
              refine ⟨122480023131329858873870705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81653348754219905915913803 122480023131329858873870705)
              ·
                refine ⟨91860017348497394155403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122480023131329858873870705 91860017348497394155403029)
                ·
                  refine ⟨4305938313210815351034517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91860017348497394155403029 4305938313210815351034517)
                  ·
                    refine ⟨201840858431756969579743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4305938313210815351034517 201840858431756969579743)
                    ·
                      rfl

theorem cell23_1179251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_1179251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179251 prefixEnd_1179251 := by exact prefixLift 1179251
  have htrace : WordTrace (prefixWord ++ tailWord_1179251) baseStart_1179251 baseEnd_1179251 := by
    simpa [prefixWord, tailWord_1179251, baseEnd_1179251] using wordTrace_append hprefix tailTrace_1179251
  have hstable : (prefixWord ++ tailWord_1179251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179251).length < 2 ^ (prefixWord ++ tailWord_1179251).sum := by decide
  have hdescent : baseEnd_1179251 < baseStart_1179251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179275 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 4, 2]
def baseStart_1179275 : Nat := 118140960795 + 1179275 * 2 ^ 59
def prefixEnd_1179275 : Nat := 4983230072969 + 3 ^ 40 * 1179275 * 2
def baseEnd_1179275 : Nat := 605534898830978814839119

theorem tailTrace_1179275 : CollatzResearch.WordTrace tailWord_1179275 prefixEnd_1179275 605534898830978814839119 := by
  unfold tailWord_1179275
  simp only [CollatzResearch.WordTrace]
  refine ⟨43011692802695553980507279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28674461868463702653671519 43011692802695553980507279)
  ·
    refine ⟨64517539204043330970760919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43011692802695553980507279 64517539204043330970760919)
    ·
      refine ⟨96776308806064996456141379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64517539204043330970760919 96776308806064996456141379)
      ·
        refine ⟨145164463209097494684212069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96776308806064996456141379 145164463209097494684212069)
        ·
          refine ⟨27218336851705780253289763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145164463209097494684212069 27218336851705780253289763)
          ·
            refine ⟨40827505277558670379934645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27218336851705780253289763 40827505277558670379934645)
            ·
              refine ⟨3827578619771125348118873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40827505277558670379934645 3827578619771125348118873)
              ·
                refine ⟨2870683964828344011089155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3827578619771125348118873 2870683964828344011089155)
                ·
                  refine ⟨4306025947242516016633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870683964828344011089155 4306025947242516016633733)
                  ·
                    refine ⟨807379865107971753118825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306025947242516016633733 807379865107971753118825)
                    ·
                      refine ⟨605534898830978814839119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807379865107971753118825 605534898830978814839119)
                      ·
                        rfl

theorem cell23_1179275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 4, 2].length) (baseStart_1179275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179275 prefixEnd_1179275 := by exact prefixLift 1179275
  have htrace : WordTrace (prefixWord ++ tailWord_1179275) baseStart_1179275 baseEnd_1179275 := by
    simpa [prefixWord, tailWord_1179275, baseEnd_1179275] using wordTrace_append hprefix tailTrace_1179275
  have hstable : (prefixWord ++ tailWord_1179275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179275).length < 2 ^ (prefixWord ++ tailWord_1179275).sum := by decide
  have hdescent : baseEnd_1179275 < baseStart_1179275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179281 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 11]
def baseStart_1179281 : Nat := 118140960795 + 1179281 * 2 ^ 59
def prefixEnd_1179281 : Nat := 4983230072969 + 3 ^ 40 * 1179281 * 2
def baseEnd_1179281 : Nat := 67281997746100643484899

theorem tailTrace_1179281 : CollatzResearch.WordTrace tailWord_1179281 prefixEnd_1179281 67281997746100643484899 := by
  unfold tailWord_1179281
  simp only [CollatzResearch.WordTrace]
  refine ⟨43011911640673817005225697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28674607760449211336817131 43011911640673817005225697)
  ·
    refine ⟨32258933730505362753919273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43011911640673817005225697 32258933730505362753919273)
    ·
      refine ⟨24194200297879022065439455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32258933730505362753919273 24194200297879022065439455)
      ·
        refine ⟨36291300446818533098159183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24194200297879022065439455 36291300446818533098159183)
        ·
          refine ⟨54436950670227799647238775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36291300446818533098159183 54436950670227799647238775)
          ·
            refine ⟨81655426005341699470858163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54436950670227799647238775 81655426005341699470858163)
            ·
              refine ⟨122483139008012549206287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81655426005341699470858163 122483139008012549206287245)
              ·
                refine ⟨45931177128004705952357717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122483139008012549206287245 45931177128004705952357717)
                ·
                  refine ⟨67281997746100643484899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 45931177128004705952357717 67281997746100643484899)
                  ·
                    rfl

theorem cell23_1179281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_1179281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179281 prefixEnd_1179281 := by exact prefixLift 1179281
  have htrace : WordTrace (prefixWord ++ tailWord_1179281) baseStart_1179281 baseEnd_1179281 := by
    simpa [prefixWord, tailWord_1179281, baseEnd_1179281] using wordTrace_append hprefix tailTrace_1179281
  have hstable : (prefixWord ++ tailWord_1179281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179281).length < 2 ^ (prefixWord ++ tailWord_1179281).sum := by decide
  have hdescent : baseEnd_1179281 < baseStart_1179281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179309 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1179309 : Nat := 118140960795 + 1179309 * 2 ^ 59
def prefixEnd_1179309 : Nat := 4983230072969 + 3 ^ 40 * 1179309 * 2
def baseEnd_1179309 : Nat := 605552357173231681813963

theorem tailTrace_1179309 : CollatzResearch.WordTrace tailWord_1179309 prefixEnd_1179309 605552357173231681813963 := by
  unfold tailWord_1179309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43012932884572377787244981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28675288589714918524829987 43012932884572377787244981)
  ·
    refine ⟨4032462457928660417554217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43012932884572377787244981 4032462457928660417554217)
    ·
      refine ⟨3024346843446495313165663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4032462457928660417554217 3024346843446495313165663)
      ·
        refine ⟨4536520265169742969748495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024346843446495313165663 4536520265169742969748495)
        ·
          refine ⟨6804780397754614454622743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536520265169742969748495 6804780397754614454622743)
          ·
            refine ⟨10207170596631921681934115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804780397754614454622743 10207170596631921681934115)
            ·
              refine ⟨15310755894947882522901173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207170596631921681934115 15310755894947882522901173)
              ·
                refine ⟨1435383365151363986521985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15310755894947882522901173 1435383365151363986521985)
                ·
                  refine ⟨1076537523863522989891489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435383365151363986521985 1076537523863522989891489)
                  ·
                    refine ⟨807403142897642242418617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076537523863522989891489 807403142897642242418617)
                    ·
                      refine ⟨605552357173231681813963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807403142897642242418617 605552357173231681813963)
                      ·
                        rfl

theorem cell23_1179309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1179309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179309 prefixEnd_1179309 := by exact prefixLift 1179309
  have htrace : WordTrace (prefixWord ++ tailWord_1179309) baseStart_1179309 baseEnd_1179309 := by
    simpa [prefixWord, tailWord_1179309, baseEnd_1179309] using wordTrace_append hprefix tailTrace_1179309
  have hstable : (prefixWord ++ tailWord_1179309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179309).length < 2 ^ (prefixWord ++ tailWord_1179309).sum := by decide
  have hdescent : baseEnd_1179309 < baseStart_1179309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179328 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 7]
def baseStart_1179328 : Nat := 118140960795 + 1179328 * 2 ^ 59
def prefixEnd_1179328 : Nat := 4983230072969 + 3 ^ 40 * 1179328 * 2
def baseEnd_1179328 : Nat := 201854037768555702492125

theorem tailTrace_1179328 : CollatzResearch.WordTrace tailWord_1179328 prefixEnd_1179328 201854037768555702492125 := by
  unfold tailWord_1179328
  simp only [CollatzResearch.WordTrace]
  refine ⟨21506812935751772016093319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28675750581002362688124425 21506812935751772016093319)
  ·
    refine ⟨32260219403627658024139979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21506812935751772016093319 32260219403627658024139979)
    ·
      refine ⟨48390329105441487036209969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32260219403627658024139979 48390329105441487036209969)
      ·
        refine ⟨36292746829081115277157477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48390329105441487036209969 36292746829081115277157477)
        ·
          refine ⟨6804890030452709114467027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36292746829081115277157477 6804890030452709114467027)
          ·
            refine ⟨10207335045679063671700541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804890030452709114467027 10207335045679063671700541)
            ·
              refine ⟨3827750642129648876887703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10207335045679063671700541 3827750642129648876887703)
              ·
                refine ⟨5741625963194473315331555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827750642129648876887703 5741625963194473315331555)
                ·
                  refine ⟨8612438944791709972997333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5741625963194473315331555 8612438944791709972997333)
                  ·
                    refine ⟨201854037768555702492125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8612438944791709972997333 201854037768555702492125)
                    ·
                      rfl

theorem cell23_1179328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_1179328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179328 prefixEnd_1179328 := by exact prefixLift 1179328
  have htrace : WordTrace (prefixWord ++ tailWord_1179328) baseStart_1179328 baseEnd_1179328 := by
    simpa [prefixWord, tailWord_1179328, baseEnd_1179328] using wordTrace_append hprefix tailTrace_1179328
  have hstable : (prefixWord ++ tailWord_1179328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179328).length < 2 ^ (prefixWord ++ tailWord_1179328).sum := by decide
  have hdescent : baseEnd_1179328 < baseStart_1179328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179332 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1179332 : Nat := 118140960795 + 1179332 * 2 ^ 59
def prefixEnd_1179332 : Nat := 4983230072969 + 3 ^ 40 * 1179332 * 2
def baseEnd_1179332 : Nat := 67284907469809454647373

theorem tailTrace_1179332 : CollatzResearch.WordTrace tailWord_1179332 prefixEnd_1179332 67284907469809454647373 := by
  unfold tailWord_1179332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21506885881744526357666125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28675847842326035143554833 21506885881744526357666125)
  ·
    refine ⟨8065082205654197384124797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21506885881744526357666125 8065082205654197384124797)
    ·
      refine ⟨3024405827120324019046799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8065082205654197384124797 3024405827120324019046799)
      ·
        refine ⟨4536608740680486028570199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024405827120324019046799 4536608740680486028570199)
        ·
          refine ⟨6804913111020729042855299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536608740680486028570199 6804913111020729042855299)
          ·
            refine ⟨10207369666531093564282949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804913111020729042855299 10207369666531093564282949)
            ·
              refine ⟨1913881812474580043303053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10207369666531093564282949 1913881812474580043303053)
              ·
                refine ⟨717705679677967516238645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913881812474580043303053 717705679677967516238645)
                ·
                  refine ⟨67284907469809454647373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 717705679677967516238645 67284907469809454647373)
                  ·
                    rfl

theorem cell23_1179332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1179332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179332 prefixEnd_1179332 := by exact prefixLift 1179332
  have htrace : WordTrace (prefixWord ++ tailWord_1179332) baseStart_1179332 baseEnd_1179332 := by
    simpa [prefixWord, tailWord_1179332, baseEnd_1179332] using wordTrace_append hprefix tailTrace_1179332
  have hstable : (prefixWord ++ tailWord_1179332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179332).length < 2 ^ (prefixWord ++ tailWord_1179332).sum := by decide
  have hdescent : baseEnd_1179332 < baseStart_1179332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179375 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 3, 4]
def baseStart_1179375 : Nat := 118140960795 + 1179375 * 2 ^ 59
def prefixEnd_1179375 : Nat := 4983230072969 + 3 ^ 40 * 1179375 * 2
def baseEnd_1179375 : Nat := 201862082298809474529553

theorem tailTrace_1179375 : CollatzResearch.WordTrace tailWord_1179375 prefixEnd_1179375 201862082298809474529553 := by
  unfold tailWord_1179375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43015340102333271059147579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28676893401555514039431719 43015340102333271059147579)
  ·
    refine ⟨64523010153499906588721369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43015340102333271059147579 64523010153499906588721369)
    ·
      refine ⟨48392257615124929941541027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64523010153499906588721369 48392257615124929941541027)
      ·
        refine ⟨72588386422687394912311541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48392257615124929941541027 72588386422687394912311541)
        ·
          refine ⟨6805161227126943273029207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72588386422687394912311541 6805161227126943273029207)
          ·
            refine ⟨10207741840690414909543811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6805161227126943273029207 10207741840690414909543811)
            ·
              refine ⟨15311612761035622364315717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207741840690414909543811 15311612761035622364315717)
              ·
                refine ⟨2870927392694179193309197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15311612761035622364315717 2870927392694179193309197)
                ·
                  refine ⟨1076597772260317197490949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2870927392694179193309197 1076597772260317197490949)
                  ·
                    refine ⟨201862082298809474529553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076597772260317197490949 201862082298809474529553)
                    ·
                      rfl

theorem cell23_1179375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_1179375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179375 prefixEnd_1179375 := by exact prefixLift 1179375
  have htrace : WordTrace (prefixWord ++ tailWord_1179375) baseStart_1179375 baseEnd_1179375 := by
    simpa [prefixWord, tailWord_1179375, baseEnd_1179375] using wordTrace_append hprefix tailTrace_1179375
  have hstable : (prefixWord ++ tailWord_1179375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179375).length < 2 ^ (prefixWord ++ tailWord_1179375).sum := by decide
  have hdescent : baseEnd_1179375 < baseStart_1179375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179388 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 10]
def baseStart_1179388 : Nat := 118140960795 + 1179388 * 2 ^ 59
def prefixEnd_1179388 : Nat := 4983230072969 + 3 ^ 40 * 1179388 * 2
def baseEnd_1179388 : Nat := 67288102460548541414011

theorem tailTrace_1179388 : CollatzResearch.WordTrace tailWord_1179388 prefixEnd_1179388 67288102460548541414011 := by
  unfold tailWord_1179388
  simp only [CollatzResearch.WordTrace]
  refine ⟨21507907125643087139685409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28677209500857449519580545 21507907125643087139685409)
  ·
    refine ⟨16130930344232315354764057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21507907125643087139685409 16130930344232315354764057)
    ·
      refine ⟨12098197758174236516073043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16130930344232315354764057 12098197758174236516073043)
      ·
        refine ⟨18147296637261354774109565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12098197758174236516073043 18147296637261354774109565)
        ·
          refine ⟨6805236238973008040291087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18147296637261354774109565 6805236238973008040291087)
          ·
            refine ⟨10207854358459512060436631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6805236238973008040291087 10207854358459512060436631)
            ·
              refine ⟨15311781537689268090654947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10207854358459512060436631 15311781537689268090654947)
              ·
                refine ⟨22967672306533902135982421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15311781537689268090654947 22967672306533902135982421)
                ·
                  refine ⟨67288102460548541414011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22967672306533902135982421 67288102460548541414011)
                  ·
                    rfl

theorem cell23_1179388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_1179388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179388 prefixEnd_1179388 := by exact prefixLift 1179388
  have htrace : WordTrace (prefixWord ++ tailWord_1179388) baseStart_1179388 baseEnd_1179388 := by
    simpa [prefixWord, tailWord_1179388, baseEnd_1179388] using wordTrace_append hprefix tailTrace_1179388
  have hstable : (prefixWord ++ tailWord_1179388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179388).length < 2 ^ (prefixWord ++ tailWord_1179388).sum := by decide
  have hdescent : baseEnd_1179388 < baseStart_1179388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179402 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1179402 : Nat := 118140960795 + 1179402 * 2 ^ 59
def prefixEnd_1179402 : Nat := 4983230072969 + 3 ^ 40 * 1179402 * 2
def baseEnd_1179402 : Nat := 605600110874099817951035

theorem tailTrace_1179402 : CollatzResearch.WordTrace tailWord_1179402 prefixEnd_1179402 605600110874099817951035 := by
  unfold tailWord_1179402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754081218308863667595115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28677549915490303113586973 10754081218308863667595115)
  ·
    refine ⟨16131121827463295501392673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10754081218308863667595115 16131121827463295501392673)
    ·
      refine ⟨12098341370597471626044505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16131121827463295501392673 12098341370597471626044505)
      ·
        refine ⟨9073756027948103719533379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098341370597471626044505 9073756027948103719533379)
        ·
          refine ⟨13610634041922155579300069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073756027948103719533379 13610634041922155579300069)
          ·
            refine ⟨2551993882860404171118763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13610634041922155579300069 2551993882860404171118763)
            ·
              refine ⟨3827990824290606256678145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551993882860404171118763 3827990824290606256678145)
              ·
                refine ⟨2870993118217954692508609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3827990824290606256678145 2870993118217954692508609)
                ·
                  refine ⟨2153244838663466019381457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870993118217954692508609 2153244838663466019381457)
                  ·
                    refine ⟨1614933628997599514536093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153244838663466019381457 1614933628997599514536093)
                    ·
                      refine ⟨605600110874099817951035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1614933628997599514536093 605600110874099817951035)
                      ·
                        rfl

theorem cell23_1179402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1179402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179402 prefixEnd_1179402 := by exact prefixLift 1179402
  have htrace : WordTrace (prefixWord ++ tailWord_1179402) baseStart_1179402 baseEnd_1179402 := by
    simpa [prefixWord, tailWord_1179402, baseEnd_1179402] using wordTrace_append hprefix tailTrace_1179402
  have hstable : (prefixWord ++ tailWord_1179402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179402).length < 2 ^ (prefixWord ++ tailWord_1179402).sum := by decide
  have hdescent : baseEnd_1179402 < baseStart_1179402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179482 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_1179482 : Nat := 118140960795 + 1179482 * 2 ^ 59
def prefixEnd_1179482 : Nat := 4983230072969 + 3 ^ 40 * 1179482 * 2
def baseEnd_1179482 : Nat := 201880396442153168316889

theorem tailTrace_1179482 : CollatzResearch.WordTrace tailWord_1179482 prefixEnd_1179482 201880396442153168316889 := by
  unfold tailWord_1179482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754810678236407083323175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28679495141963752222195133 10754810678236407083323175)
  ·
    refine ⟨16132216017354610624984763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10754810678236407083323175 16132216017354610624984763)
    ·
      refine ⟨24198324026031915937477145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16132216017354610624984763 24198324026031915937477145)
      ·
        refine ⟨18148743019523936953107859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24198324026031915937477145 18148743019523936953107859)
        ·
          refine ⟨27223114529285905429661789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18148743019523936953107859 27223114529285905429661789)
          ·
            refine ⟨10208667948482214536123171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27223114529285905429661789 10208667948482214536123171)
            ·
              refine ⟨15313001922723321804184757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10208667948482214536123171 15313001922723321804184757)
              ·
                refine ⟨1435593930255311419142321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15313001922723321804184757 1435593930255311419142321)
                ·
                  refine ⟨1076695447691483564356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435593930255311419142321 1076695447691483564356741)
                  ·
                    refine ⟨201880396442153168316889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076695447691483564356741 201880396442153168316889)
                    ·
                      rfl

theorem cell23_1179482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_1179482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179482 prefixEnd_1179482 := by exact prefixLift 1179482
  have htrace : WordTrace (prefixWord ++ tailWord_1179482) baseStart_1179482 baseEnd_1179482 := by
    simpa [prefixWord, tailWord_1179482, baseEnd_1179482] using wordTrace_append hprefix tailTrace_1179482
  have hstable : (prefixWord ++ tailWord_1179482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179482).length < 2 ^ (prefixWord ++ tailWord_1179482).sum := by decide
  have hdescent : baseEnd_1179482 < baseStart_1179482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179489 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_1179489 : Nat := 118140960795 + 1179489 * 2 ^ 59
def prefixEnd_1179489 : Nat := 4983230072969 + 3 ^ 40 * 1179489 * 2
def baseEnd_1179489 : Nat := 605644783691040977563135

theorem tailTrace_1179489 : CollatzResearch.WordTrace tailWord_1179489 prefixEnd_1179489 605644783691040977563135 := by
  unfold tailWord_1179489
  simp only [CollatzResearch.WordTrace]
  refine ⟨43019498023920268528797521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28679665349280179019198347 43019498023920268528797521)
  ·
    refine ⟨32264623517940201396598141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43019498023920268528797521 32264623517940201396598141)
    ·
      refine ⟨12099233819227575523724303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32264623517940201396598141 12099233819227575523724303)
      ·
        refine ⟨18148850728841363285586455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12099233819227575523724303 18148850728841363285586455)
        ·
          refine ⟨27223276093262044928379683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18148850728841363285586455 27223276093262044928379683)
          ·
            refine ⟨40834914139893067392569525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27223276093262044928379683 40834914139893067392569525)
            ·
              refine ⟨3828273200614975068053393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40834914139893067392569525 3828273200614975068053393)
              ·
                refine ⟨2871204900461231301040045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828273200614975068053393 2871204900461231301040045)
                ·
                  refine ⟨1076701837672961737890017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2871204900461231301040045 1076701837672961737890017)
                  ·
                    refine ⟨807526378254721303417513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076701837672961737890017 807526378254721303417513)
                    ·
                      refine ⟨605644783691040977563135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807526378254721303417513 605644783691040977563135)
                      ·
                        rfl

theorem cell23_1179489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_1179489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179489 prefixEnd_1179489 := by exact prefixLift 1179489
  have htrace : WordTrace (prefixWord ++ tailWord_1179489) baseStart_1179489 baseEnd_1179489 := by
    simpa [prefixWord, tailWord_1179489, baseEnd_1179489] using wordTrace_append hprefix tailTrace_1179489
  have hstable : (prefixWord ++ tailWord_1179489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179489).length < 2 ^ (prefixWord ++ tailWord_1179489).sum := by decide
  have hdescent : baseEnd_1179489 < baseStart_1179489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179509 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1179509 : Nat := 118140960795 + 1179509 * 2 ^ 59
def prefixEnd_1179509 : Nat := 4983230072969 + 3 ^ 40 * 1179509 * 2
def baseEnd_1179509 : Nat := 605655053304130899313043

theorem tailTrace_1179509 : CollatzResearch.WordTrace tailWord_1179509 prefixEnd_1179509 605655053304130899313043 := by
  unfold tailWord_1179509
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020227483847811944525581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28680151655898541296350387 43020227483847811944525581)
  ·
    refine ⟨16132585306442929479197093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43020227483847811944525581 16132585306442929479197093)
    ·
      refine ⟨3024859744958049277349455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16132585306442929479197093 3024859744958049277349455)
      ·
        refine ⟨4537289617437073916024183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024859744958049277349455 4537289617437073916024183)
        ·
          refine ⟨6805934426155610874036275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537289617437073916024183 6805934426155610874036275)
          ·
            refine ⟨10208901639233416311054413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6805934426155610874036275 10208901639233416311054413)
            ·
              refine ⟨3828338114712531116645405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10208901639233416311054413 3828338114712531116645405)
              ·
                refine ⟨1435626793017199168742027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3828338114712531116645405 1435626793017199168742027)
                ·
                  refine ⟨2153440189525798753113041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435626793017199168742027 2153440189525798753113041)
                  ·
                    refine ⟨1615080142144349064834781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153440189525798753113041 1615080142144349064834781)
                    ·
                      refine ⟨605655053304130899313043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615080142144349064834781 605655053304130899313043)
                      ·
                        rfl

theorem cell23_1179509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1179509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179509 prefixEnd_1179509 := by exact prefixLift 1179509
  have htrace : WordTrace (prefixWord ++ tailWord_1179509) baseStart_1179509 baseEnd_1179509 := by
    simpa [prefixWord, tailWord_1179509, baseEnd_1179509] using wordTrace_append hprefix tailTrace_1179509
  have hstable : (prefixWord ++ tailWord_1179509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179509).length < 2 ^ (prefixWord ++ tailWord_1179509).sum := by decide
  have hdescent : baseEnd_1179509 < baseStart_1179509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179545 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1179545 : Nat := 118140960795 + 1179545 * 2 ^ 59
def prefixEnd_1179545 : Nat := 4983230072969 + 3 ^ 40 * 1179545 * 2
def baseEnd_1179545 : Nat := 605673538607692758462877

theorem tailTrace_1179545 : CollatzResearch.WordTrace tailWord_1179545 prefixEnd_1179545 605673538607692758462877 := by
  unfold tailWord_1179545
  simp only [CollatzResearch.WordTrace]
  refine ⟨43021540511717390092836089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28681027007811593395224059 43021540511717390092836089)
  ·
    refine ⟨32266155383788042569627067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43021540511717390092836089 32266155383788042569627067)
    ·
      refine ⟨48399233075682063854440601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32266155383788042569627067 48399233075682063854440601)
      ·
        refine ⟨36299424806761547890830451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48399233075682063854440601 36299424806761547890830451)
        ·
          refine ⟨54449137210142321836245677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36299424806761547890830451 54449137210142321836245677)
          ·
            refine ⟨20418426453803370688592129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54449137210142321836245677 20418426453803370688592129)
            ·
              refine ⟨15313819840352528016444097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20418426453803370688592129 15313819840352528016444097)
              ·
                refine ⟨11485364880264396012333073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15313819840352528016444097 11485364880264396012333073)
                ·
                  refine ⟨8614023660198297009249805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11485364880264396012333073 8614023660198297009249805)
                  ·
                    refine ⟨3230258872574361378468677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8614023660198297009249805 3230258872574361378468677)
                    ·
                      refine ⟨605673538607692758462877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3230258872574361378468677 605673538607692758462877)
                      ·
                        rfl

theorem cell23_1179545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1179545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179545 prefixEnd_1179545 := by exact prefixLift 1179545
  have htrace : WordTrace (prefixWord ++ tailWord_1179545) baseStart_1179545 baseEnd_1179545 := by
    simpa [prefixWord, tailWord_1179545, baseEnd_1179545] using wordTrace_append hprefix tailTrace_1179545
  have hstable : (prefixWord ++ tailWord_1179545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179545).length < 2 ^ (prefixWord ++ tailWord_1179545).sum := by decide
  have hdescent : baseEnd_1179545 < baseStart_1179545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179632 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_1179632 : Nat := 118140960795 + 1179632 * 2 ^ 59
def prefixEnd_1179632 : Nat := 4983230072969 + 3 ^ 40 * 1179632 * 2
def baseEnd_1179632 : Nat := 201906070474877972691659

theorem tailTrace_1179632 : CollatzResearch.WordTrace tailWord_1179632 prefixEnd_1179632 201906070474877972691659 := by
  unfold tailWord_1179632
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512356831201101975626575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28683142441601469300835433 21512356831201101975626575)
  ·
    refine ⟨32268535246801652963439863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21512356831201101975626575 32268535246801652963439863)
    ·
      refine ⟨48402802870202479445159795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32268535246801652963439863 48402802870202479445159795)
      ·
        refine ⟨72604204305303719167739693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48402802870202479445159795 72604204305303719167739693)
        ·
          refine ⟨27226576614488894687902385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72604204305303719167739693 27226576614488894687902385)
          ·
            refine ⟨20419932460866671015926789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27226576614488894687902385 20419932460866671015926789)
            ·
              refine ⟨3828737336412500815486273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20419932460866671015926789 3828737336412500815486273)
              ·
                refine ⟨2871553002309375611614705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828737336412500815486273 2871553002309375611614705)
                ·
                  refine ⟨2153664751732031708711029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871553002309375611614705 2153664751732031708711029)
                  ·
                    refine ⟨201906070474877972691659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2153664751732031708711029 201906070474877972691659)
                    ·
                      rfl

theorem cell23_1179632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_1179632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179632 prefixEnd_1179632 := by exact prefixLift 1179632
  have htrace : WordTrace (prefixWord ++ tailWord_1179632) baseStart_1179632 baseEnd_1179632 := by
    simpa [prefixWord, tailWord_1179632, baseEnd_1179632] using wordTrace_append hprefix tailTrace_1179632
  have hstable : (prefixWord ++ tailWord_1179632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179632).length < 2 ^ (prefixWord ++ tailWord_1179632).sum := by decide
  have hdescent : baseEnd_1179632 < baseStart_1179632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179646 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1179646 : Nat := 118140960795 + 1179646 * 2 ^ 59
def prefixEnd_1179646 : Nat := 4983230072969 + 3 ^ 40 * 1179646 * 2
def baseEnd_1179646 : Nat := 605725400153796863299913

theorem tailTrace_1179646 : CollatzResearch.WordTrace tailWord_1179646 prefixEnd_1179646 605725400153796863299913 := by
  unfold tailWord_1179646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378153035543935542782849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28683482856234322894841861 5378153035543935542782849)
  ·
    refine ⟨4033614776657951657087137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5378153035543935542782849 4033614776657951657087137)
    ·
      refine ⟨3025211082493463742815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4033614776657951657087137 3025211082493463742815353)
      ·
        refine ⟨2268908311870097807111515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3025211082493463742815353 2268908311870097807111515)
        ·
          refine ⟨3403362467805146710667273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268908311870097807111515 3403362467805146710667273)
          ·
            refine ⟨2552521850853860033000455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3403362467805146710667273 2552521850853860033000455)
            ·
              refine ⟨3828782776280790049500683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552521850853860033000455 3828782776280790049500683)
              ·
                refine ⟨5743174164421185074251025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828782776280790049500683 5743174164421185074251025)
                ·
                  refine ⟨4307380623315888805688269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743174164421185074251025 4307380623315888805688269)
                  ·
                    refine ⟨1615267733743458302133101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4307380623315888805688269 1615267733743458302133101)
                    ·
                      refine ⟨605725400153796863299913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615267733743458302133101 605725400153796863299913)
                      ·
                        rfl

theorem cell23_1179646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1179646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179646 prefixEnd_1179646 := by exact prefixLift 1179646
  have htrace : WordTrace (prefixWord ++ tailWord_1179646) baseStart_1179646 baseEnd_1179646 := by
    simpa [prefixWord, tailWord_1179646, baseEnd_1179646] using wordTrace_append hprefix tailTrace_1179646
  have hstable : (prefixWord ++ tailWord_1179646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179646).length < 2 ^ (prefixWord ++ tailWord_1179646).sum := by decide
  have hdescent : baseEnd_1179646 < baseStart_1179646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179669 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1179669 : Nat := 118140960795 + 1179669 * 2 ^ 59
def prefixEnd_1179669 : Nat := 4983230072969 + 3 ^ 40 * 1179669 * 2
def baseEnd_1179669 : Nat := 605737210208850273312307

theorem tailTrace_1179669 : CollatzResearch.WordTrace tailWord_1179669 prefixEnd_1179669 605737210208850273312307 := by
  unfold tailWord_1179669
  simp only [CollatzResearch.WordTrace]
  refine ⟨43026063163268159270350061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28684042108845439513566707 43026063163268159270350061)
  ·
    refine ⟨16134773686225559726381273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43026063163268159270350061 16134773686225559726381273)
    ·
      refine ⟨12101080264669169794785955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16134773686225559726381273 12101080264669169794785955)
      ·
        refine ⟨18151620397003754692178933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12101080264669169794785955 18151620397003754692178933)
        ·
          refine ⟨1701714412219102002391775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18151620397003754692178933 1701714412219102002391775)
          ·
            refine ⟨2552571618328653003587663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701714412219102002391775 2552571618328653003587663)
            ·
              refine ⟨3828857427492979505381495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552571618328653003587663 3828857427492979505381495)
              ·
                refine ⟨5743286141239469258072243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828857427492979505381495 5743286141239469258072243)
                ·
                  refine ⟨8614929211859203887108365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743286141239469258072243 8614929211859203887108365)
                  ·
                    refine ⟨3230598454447201457665637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8614929211859203887108365 3230598454447201457665637)
                    ·
                      refine ⟨605737210208850273312307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3230598454447201457665637 605737210208850273312307)
                      ·
                        rfl

theorem cell23_1179669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1179669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179669 prefixEnd_1179669 := by exact prefixLift 1179669
  have htrace : WordTrace (prefixWord ++ tailWord_1179669) baseStart_1179669 baseEnd_1179669 := by
    simpa [prefixWord, tailWord_1179669, baseEnd_1179669] using wordTrace_append hprefix tailTrace_1179669
  have hstable : (prefixWord ++ tailWord_1179669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179669).length < 2 ^ (prefixWord ++ tailWord_1179669).sum := by decide
  have hdescent : baseEnd_1179669 < baseStart_1179669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179682 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1179682 : Nat := 118140960795 + 1179682 * 2 ^ 59
def prefixEnd_1179682 : Nat := 4983230072969 + 3 ^ 40 * 1179682 * 2
def baseEnd_1179682 : Nat := 605743885457358722449747

theorem tailTrace_1179682 : CollatzResearch.WordTrace tailWord_1179682 prefixEnd_1179682 605743885457358722449747 := by
  unfold tailWord_1179682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756634328055265622643325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28684358208147374993715533 10756634328055265622643325)
  ·
    refine ⟨4033737873020724608491247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10756634328055265622643325 4033737873020724608491247)
    ·
      refine ⟨6050606809531086912736871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033737873020724608491247 6050606809531086912736871)
      ·
        refine ⟨9075910214296630369105307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050606809531086912736871 9075910214296630369105307)
        ·
          refine ⟨13613865321444945553657961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075910214296630369105307 13613865321444945553657961)
          ·
            refine ⟨10210398991083709165243471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13613865321444945553657961 10210398991083709165243471)
            ·
              refine ⟨15315598486625563747865207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10210398991083709165243471 15315598486625563747865207)
              ·
                refine ⟨22973397729938345621797811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15315598486625563747865207 22973397729938345621797811)
                ·
                  refine ⟨34460096594907518432696717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22973397729938345621797811 34460096594907518432696717)
                  ·
                    refine ⟨12922536223090319412261269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34460096594907518432696717 12922536223090319412261269)
                    ·
                      refine ⟨605743885457358722449747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12922536223090319412261269 605743885457358722449747)
                      ·
                        rfl

theorem cell23_1179682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1179682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179682 prefixEnd_1179682 := by exact prefixLift 1179682
  have htrace : WordTrace (prefixWord ++ tailWord_1179682) baseStart_1179682 baseEnd_1179682 := by
    simpa [prefixWord, tailWord_1179682, baseEnd_1179682] using wordTrace_append hprefix tailTrace_1179682
  have hstable : (prefixWord ++ tailWord_1179682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179682).length < 2 ^ (prefixWord ++ tailWord_1179682).sum := by decide
  have hdescent : baseEnd_1179682 < baseStart_1179682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179692 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 6]
def baseStart_1179692 : Nat := 118140960795 + 1179692 * 2 ^ 59
def prefixEnd_1179692 : Nat := 4983230072969 + 3 ^ 40 * 1179692 * 2
def baseEnd_1179692 : Nat := 67305446695989298147189

theorem tailTrace_1179692 : CollatzResearch.WordTrace tailWord_1179692 prefixEnd_1179692 67305446695989298147189 := by
  unfold tailWord_1179692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21513451021092417099218665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28684601361456556132291553 21513451021092417099218665)
  ·
    refine ⟨16135088265819312824413999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21513451021092417099218665 16135088265819312824413999)
    ·
      refine ⟨24202632398728969236620999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16135088265819312824413999 24202632398728969236620999)
      ·
        refine ⟨36303948598093453854931499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24202632398728969236620999 36303948598093453854931499)
        ·
          refine ⟨54455922897140180782397249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36303948598093453854931499 54455922897140180782397249)
          ·
            refine ⟨40841942172855135586797937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54455922897140180782397249 40841942172855135586797937)
            ·
              refine ⟨30631456629641351690098453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40841942172855135586797937 30631456629641351690098453)
              ·
                refine ⟨1435849529514438360473365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30631456629641351690098453 1435849529514438360473365)
                ·
                  refine ⟨67305446695989298147189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1435849529514438360473365 67305446695989298147189)
                  ·
                    rfl

theorem cell23_1179692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_1179692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179692 prefixEnd_1179692 := by exact prefixLift 1179692
  have htrace : WordTrace (prefixWord ++ tailWord_1179692) baseStart_1179692 baseEnd_1179692 := by
    simpa [prefixWord, tailWord_1179692, baseEnd_1179692] using wordTrace_append hprefix tailTrace_1179692
  have hstable : (prefixWord ++ tailWord_1179692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179692).length < 2 ^ (prefixWord ++ tailWord_1179692).sum := by decide
  have hdescent : baseEnd_1179692 < baseStart_1179692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179696 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 1, 4]
def baseStart_1179696 : Nat := 118140960795 + 1179696 * 2 ^ 59
def prefixEnd_1179696 : Nat := 4983230072969 + 3 ^ 40 * 1179696 * 2
def baseEnd_1179696 : Nat := 201917024728840555891561

theorem tailTrace_1179696 : CollatzResearch.WordTrace tailWord_1179696 prefixEnd_1179696 201917024728840555891561 := by
  unfold tailWord_1179696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21513523967085171440791471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28684698622780228587721961 21513523967085171440791471)
  ·
    refine ⟨32270285950627757161187207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21513523967085171440791471 32270285950627757161187207)
    ·
      refine ⟨48405428925941635741780811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32270285950627757161187207 48405428925941635741780811)
      ·
        refine ⟨72608143388912453612671217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48405428925941635741780811 72608143388912453612671217)
        ·
          refine ⟨54456107541684340209503413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72608143388912453612671217 54456107541684340209503413)
          ·
            refine ⟨5105260082032906894640945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54456107541684340209503413 5105260082032906894640945)
            ·
              refine ⟨3828945061524680170980709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105260082032906894640945 3828945061524680170980709)
              ·
                refine ⟨717927199035877532058883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3828945061524680170980709 717927199035877532058883)
                ·
                  refine ⟨1076890798553816298088325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717927199035877532058883 1076890798553816298088325)
                  ·
                    refine ⟨201917024728840555891561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076890798553816298088325 201917024728840555891561)
                    ·
                      rfl

theorem cell23_1179696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 4].length) (baseStart_1179696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179696 prefixEnd_1179696 := by exact prefixLift 1179696
  have htrace : WordTrace (prefixWord ++ tailWord_1179696) baseStart_1179696 baseEnd_1179696 := by
    simpa [prefixWord, tailWord_1179696, baseEnd_1179696] using wordTrace_append hprefix tailTrace_1179696
  have hstable : (prefixWord ++ tailWord_1179696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179696).length < 2 ^ (prefixWord ++ tailWord_1179696).sum := by decide
  have hdescent : baseEnd_1179696 < baseStart_1179696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179730 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1179730 : Nat := 118140960795 + 1179730 * 2 ^ 59
def prefixEnd_1179730 : Nat := 4983230072969 + 3 ^ 40 * 1179730 * 2
def baseEnd_1179730 : Nat := 201922844176258178216509

theorem tailTrace_1179730 : CollatzResearch.WordTrace tailWord_1179730 prefixEnd_1179730 201922844176258178216509 := by
  unfold tailWord_1179730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757072004011791672080161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28685525344031444458880429 10757072004011791672080161)
  ·
    refine ⟨8067804003008843754060121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757072004011791672080161 8067804003008843754060121)
    ·
      refine ⟨6050853002256632815545091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8067804003008843754060121 6050853002256632815545091)
      ·
        refine ⟨9076279503384949223317637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050853002256632815545091 9076279503384949223317637)
        ·
          refine ⟨1701802406884677979372057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9076279503384949223317637 1701802406884677979372057)
          ·
            refine ⟨1276351805163508484529043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701802406884677979372057 1276351805163508484529043)
            ·
              refine ⟨1914527707745262726793565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276351805163508484529043 1914527707745262726793565)
              ·
                refine ⟨717947890404473522547587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914527707745262726793565 717947890404473522547587)
                ·
                  refine ⟨1076921835606710283821381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717947890404473522547587 1076921835606710283821381)
                  ·
                    refine ⟨201922844176258178216509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076921835606710283821381 201922844176258178216509)
                    ·
                      rfl

theorem cell23_1179730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1179730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179730 prefixEnd_1179730 := by exact prefixLift 1179730
  have htrace : WordTrace (prefixWord ++ tailWord_1179730) baseStart_1179730 baseEnd_1179730 := by
    simpa [prefixWord, tailWord_1179730, baseEnd_1179730] using wordTrace_append hprefix tailTrace_1179730
  have hstable : (prefixWord ++ tailWord_1179730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179730).length < 2 ^ (prefixWord ++ tailWord_1179730).sum := by decide
  have hdescent : baseEnd_1179730 < baseStart_1179730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179776 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2]
def baseStart_1179776 : Nat := 118140960795 + 1179776 * 2 ^ 59
def prefixEnd_1179776 : Nat := 4983230072969 + 3 ^ 40 * 1179776 * 2
def baseEnd_1179776 : Nat := 605792152638881354674315

theorem tailTrace_1179776 : CollatzResearch.WordTrace tailWord_1179776 prefixEnd_1179776 605792152638881354674315 := by
  unfold tailWord_1179776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21514982886940258272247591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28686643849253677696330121 21514982886940258272247591)
  ·
    refine ⟨32272474330410387408371387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21514982886940258272247591 32272474330410387408371387)
    ·
      refine ⟨48408711495615581112557081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32272474330410387408371387 48408711495615581112557081)
      ·
        refine ⟨36306533621711685834417811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48408711495615581112557081 36306533621711685834417811)
        ·
          refine ⟨54459800432567528751626717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36306533621711685834417811 54459800432567528751626717)
          ·
            refine ⟨20422425162212823281860019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54459800432567528751626717 20422425162212823281860019)
            ·
              refine ⟨30633637743319234922790029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20422425162212823281860019 30633637743319234922790029)
              ·
                refine ⟨11487614153744713096046261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30633637743319234922790029 11487614153744713096046261)
                ·
                  refine ⟨1076963826913566852754337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11487614153744713096046261 1076963826913566852754337)
                  ·
                    refine ⟨807722870185175139565753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1076963826913566852754337 807722870185175139565753)
                    ·
                      refine ⟨605792152638881354674315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807722870185175139565753 605792152638881354674315)
                      ·
                        rfl

theorem cell23_1179776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_1179776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179776 prefixEnd_1179776 := by exact prefixLift 1179776
  have htrace : WordTrace (prefixWord ++ tailWord_1179776) baseStart_1179776 baseEnd_1179776 := by
    simpa [prefixWord, tailWord_1179776, baseEnd_1179776] using wordTrace_append hprefix tailTrace_1179776
  have hstable : (prefixWord ++ tailWord_1179776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179776).length < 2 ^ (prefixWord ++ tailWord_1179776).sum := by decide
  have hdescent : baseEnd_1179776 < baseStart_1179776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179798 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1179798 : Nat := 118140960795 + 1179798 * 2 ^ 59
def prefixEnd_1179798 : Nat := 4983230072969 + 3 ^ 40 * 1179798 * 2
def baseEnd_1179798 : Nat := 201934483071093422866405

theorem tailTrace_1179798 : CollatzResearch.WordTrace tailWord_1179798 prefixEnd_1179798 201934483071093422866405 := by
  unfold tailWord_1179798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689423011237550893862253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28687178786533876201197365 2689423011237550893862253)
  ·
    refine ⟨1008533629214081585198345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2689423011237550893862253 1008533629214081585198345)
    ·
      refine ⟨756400221910561188898759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1008533629214081585198345 756400221910561188898759)
      ·
        refine ⟨1134600332865841783348139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756400221910561188898759 1134600332865841783348139)
        ·
          refine ⟨1701900499298762675022209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134600332865841783348139 1701900499298762675022209)
          ·
            refine ⟨1276425374474072006266657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701900499298762675022209 1276425374474072006266657)
            ·
              refine ⟨957319030855554004699993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276425374474072006266657 957319030855554004699993)
              ·
                refine ⟨717989273141665503524995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957319030855554004699993 717989273141665503524995)
                ·
                  refine ⟨1076983909712498255287493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717989273141665503524995 1076983909712498255287493)
                  ·
                    refine ⟨201934483071093422866405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1076983909712498255287493 201934483071093422866405)
                    ·
                      rfl

theorem cell23_1179798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1179798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179798 prefixEnd_1179798 := by exact prefixLift 1179798
  have htrace : WordTrace (prefixWord ++ tailWord_1179798) baseStart_1179798 baseEnd_1179798 := by
    simpa [prefixWord, tailWord_1179798, baseEnd_1179798] using wordTrace_append hprefix tailTrace_1179798
  have hstable : (prefixWord ++ tailWord_1179798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179798).length < 2 ^ (prefixWord ++ tailWord_1179798).sum := by decide
  have hdescent : baseEnd_1179798 < baseStart_1179798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179799 : List Nat := [1, 1, 3, 3, 5, 10]
def baseStart_1179799 : Nat := 118140960795 + 1179799 * 2 ^ 59
def prefixEnd_1179799 : Nat := 4983230072969 + 3 ^ 40 * 1179799 * 2
def baseEnd_1179799 : Nat := 2493020422608785039863

theorem tailTrace_1179799 : CollatzResearch.WordTrace tailWord_1179799 prefixEnd_1179799 2493020422608785039863 := by
  unfold tailWord_1179799
  simp only [CollatzResearch.WordTrace]
  refine ⟨43030804652797191472582451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28687203101864794315054967 43030804652797191472582451)
  ·
    refine ⟨64546206979195787208873677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43030804652797191472582451 64546206979195787208873677)
    ·
      refine ⟨24204827617198420203327629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64546206979195787208873677 24204827617198420203327629)
      ·
        refine ⟨9076810356449407576247861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24204827617198420203327629 9076810356449407576247861)
        ·
          refine ⟨850950970917131960273237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9076810356449407576247861 850950970917131960273237)
          ·
            refine ⟨2493020422608785039863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 850950970917131960273237 2493020422608785039863)
            ·
              rfl

theorem cell23_1179799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 10].length) (baseStart_1179799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179799 prefixEnd_1179799 := by exact prefixLift 1179799
  have htrace : WordTrace (prefixWord ++ tailWord_1179799) baseStart_1179799 baseEnd_1179799 := by
    simpa [prefixWord, tailWord_1179799, baseEnd_1179799] using wordTrace_append hprefix tailTrace_1179799
  have hstable : (prefixWord ++ tailWord_1179799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179799).length < 2 ^ (prefixWord ++ tailWord_1179799).sum := by decide
  have hdescent : baseEnd_1179799 < baseStart_1179799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179826 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1179826 : Nat := 118140960795 + 1179826 * 2 ^ 59
def prefixEnd_1179826 : Nat := 4983230072969 + 3 ^ 40 * 1179826 * 2
def baseEnd_1179826 : Nat := 605817826671606159049085

theorem tailTrace_1179826 : CollatzResearch.WordTrace tailWord_1179826 prefixEnd_1179826 605817826671606159049085 := by
  unfold tailWord_1179826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757947355924843770953833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28687859615799583389210221 10757947355924843770953833)
  ·
    refine ⟨8068460516943632828215375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757947355924843770953833 8068460516943632828215375)
    ·
      refine ⟨12102690775415449242323063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068460516943632828215375 12102690775415449242323063)
      ·
        refine ⟨18154036163123173863484595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12102690775415449242323063 18154036163123173863484595)
        ·
          refine ⟨27231054244684760795226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18154036163123173863484595 27231054244684760795226893)
          ·
            refine ⟨10211645341756785298210085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27231054244684760795226893 10211645341756785298210085)
            ·
              refine ⟨1914683501579397243414391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10211645341756785298210085 1914683501579397243414391)
              ·
                refine ⟨2872025252369095865121587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914683501579397243414391 2872025252369095865121587)
                ·
                  refine ⟨4308037878553643797682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872025252369095865121587 4308037878553643797682381)
                  ·
                    refine ⟨1615514204457616424130893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4308037878553643797682381 1615514204457616424130893)
                    ·
                      refine ⟨605817826671606159049085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615514204457616424130893 605817826671606159049085)
                      ·
                        rfl

theorem cell23_1179826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1179826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179826 prefixEnd_1179826 := by exact prefixLift 1179826
  have htrace : WordTrace (prefixWord ++ tailWord_1179826) baseStart_1179826 baseEnd_1179826 := by
    simpa [prefixWord, tailWord_1179826, baseEnd_1179826] using wordTrace_append hprefix tailTrace_1179826
  have hstable : (prefixWord ++ tailWord_1179826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179826).length < 2 ^ (prefixWord ++ tailWord_1179826).sum := by decide
  have hdescent : baseEnd_1179826 < baseStart_1179826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179866 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_1179866 : Nat := 118140960795 + 1179866 * 2 ^ 59
def prefixEnd_1179866 : Nat := 4983230072969 + 3 ^ 40 * 1179866 * 2
def baseEnd_1179866 : Nat := 605838365897786002548901

theorem tailTrace_1179866 : CollatzResearch.WordTrace tailWord_1179866 prefixEnd_1179866 605838365897786002548901 := by
  unfold tailWord_1179866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758312085888615478817863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28688832229036307943514301 10758312085888615478817863)
  ·
    refine ⟨16137468128832923218226795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10758312085888615478817863 16137468128832923218226795)
    ·
      refine ⟨24206202193249384827340193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16137468128832923218226795 24206202193249384827340193)
      ·
        refine ⟨18154651644937038620505145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24206202193249384827340193 18154651644937038620505145)
        ·
          refine ⟨13615988733702778965378859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18154651644937038620505145 13615988733702778965378859)
          ·
            refine ⟨20423983100554168448068289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13615988733702778965378859 20423983100554168448068289)
            ·
              refine ⟨15317987325415626336051217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20423983100554168448068289 15317987325415626336051217)
              ·
                refine ⟨11488490494061719752038413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15317987325415626336051217 11488490494061719752038413)
                ·
                  refine ⟨4308183935273144907014405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11488490494061719752038413 4308183935273144907014405)
                  ·
                    refine ⟨807784487863714670065201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308183935273144907014405 807784487863714670065201)
                    ·
                      refine ⟨605838365897786002548901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807784487863714670065201 605838365897786002548901)
                      ·
                        rfl

theorem cell23_1179866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_1179866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179866 prefixEnd_1179866 := by exact prefixLift 1179866
  have htrace : WordTrace (prefixWord ++ tailWord_1179866) baseStart_1179866 baseEnd_1179866 := by
    simpa [prefixWord, tailWord_1179866, baseEnd_1179866] using wordTrace_append hprefix tailTrace_1179866
  have hstable : (prefixWord ++ tailWord_1179866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179866).length < 2 ^ (prefixWord ++ tailWord_1179866).sum := by decide
  have hdescent : baseEnd_1179866 < baseStart_1179866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179874 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1179874 : Nat := 118140960795 + 1179874 * 2 ^ 59
def prefixEnd_1179874 : Nat := 4983230072969 + 3 ^ 40 * 1179874 * 2
def baseEnd_1179874 : Nat := 605842473743021971248865

theorem tailTrace_1179874 : CollatzResearch.WordTrace tailWord_1179874 prefixEnd_1179874 605842473743021971248865 := by
  unfold tailWord_1179874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758385031881369820390669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28689026751683652854375117 10758385031881369820390669)
  ·
    refine ⟨4034394386955513682646501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10758385031881369820390669 4034394386955513682646501)
    ·
      refine ⟨756448947554158815496219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4034394386955513682646501 756448947554158815496219)
      ·
        refine ⟨1134673421331238223244329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756448947554158815496219 1134673421331238223244329)
        ·
          refine ⟨851005065998428667433247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134673421331238223244329 851005065998428667433247)
          ·
            refine ⟨1276507598997643001149871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851005065998428667433247 1276507598997643001149871)
            ·
              refine ⟨1914761398496464501724807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276507598997643001149871 1914761398496464501724807)
              ·
                refine ⟨2872142097744696752587211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914761398496464501724807 2872142097744696752587211)
                ·
                  refine ⟨4308213146617045128880817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872142097744696752587211 4308213146617045128880817)
                  ·
                    refine ⟨3231159859962783846660613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4308213146617045128880817 3231159859962783846660613)
                    ·
                      refine ⟨605842473743021971248865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3231159859962783846660613 605842473743021971248865)
                      ·
                        rfl

theorem cell23_1179874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1179874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179874 prefixEnd_1179874 := by exact prefixLift 1179874
  have htrace : WordTrace (prefixWord ++ tailWord_1179874) baseStart_1179874 baseEnd_1179874 := by
    simpa [prefixWord, tailWord_1179874, baseEnd_1179874] using wordTrace_append hprefix tailTrace_1179874
  have hstable : (prefixWord ++ tailWord_1179874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179874).length < 2 ^ (prefixWord ++ tailWord_1179874).sum := by decide
  have hdescent : baseEnd_1179874 < baseStart_1179874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179889 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 7]
def baseStart_1179889 : Nat := 118140960795 + 1179889 * 2 ^ 59
def prefixEnd_1179889 : Nat := 4983230072969 + 3 ^ 40 * 1179889 * 2
def baseEnd_1179889 : Nat := 67316686216982156951255

theorem tailTrace_1179889 : CollatzResearch.WordTrace tailWord_1179889 prefixEnd_1179889 67316686216982156951255 := by
  unfold tailWord_1179889
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034087222471136843358721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28689391481647424562239147 43034087222471136843358721)
  ·
    refine ⟨32275565416853352632519041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43034087222471136843358721 32275565416853352632519041)
    ·
      refine ⟨24206674062640014474389281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32275565416853352632519041 24206674062640014474389281)
      ·
        refine ⟨18155005546980010855791961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24206674062640014474389281 18155005546980010855791961)
        ·
          refine ⟨13616254160235008141843971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18155005546980010855791961 13616254160235008141843971)
          ·
            refine ⟨20424381240352512212765957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13616254160235008141843971 20424381240352512212765957)
            ·
              refine ⟨3829571482566096039893617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20424381240352512212765957 3829571482566096039893617)
              ·
                refine ⟨2872178611924572029920213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3829571482566096039893617 2872178611924572029920213)
                ·
                  refine ⟨67316686216982156951255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2872178611924572029920213 67316686216982156951255)
                  ·
                    rfl

theorem cell23_1179889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_1179889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179889 prefixEnd_1179889 := by exact prefixLift 1179889
  have htrace : WordTrace (prefixWord ++ tailWord_1179889) baseStart_1179889 baseEnd_1179889 := by
    simpa [prefixWord, tailWord_1179889, baseEnd_1179889] using wordTrace_append hprefix tailTrace_1179889
  have hstable : (prefixWord ++ tailWord_1179889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179889).length < 2 ^ (prefixWord ++ tailWord_1179889).sum := by decide
  have hdescent : baseEnd_1179889 < baseStart_1179889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179934 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1179934 : Nat := 118140960795 + 1179934 * 2 ^ 59
def prefixEnd_1179934 : Nat := 4983230072969 + 3 ^ 40 * 1179934 * 2
def baseEnd_1179934 : Nat := 605873282582291736498589

theorem tailTrace_1179934 : CollatzResearch.WordTrace tailWord_1179934 prefixEnd_1179934 605873282582291736498589 := by
  unfold tailWord_1179934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379466063413513691093357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28690485671538739685831237 5379466063413513691093357)
  ·
    refine ⟨2017299773780067634160009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5379466063413513691093357 2017299773780067634160009)
    ·
      refine ⟨1512974830335050725620007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2017299773780067634160009 1512974830335050725620007)
      ·
        refine ⟨2269462245502576088430011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512974830335050725620007 2269462245502576088430011)
        ·
          refine ⟨3404193368253864132645017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269462245502576088430011 3404193368253864132645017)
          ·
            refine ⟨2553145026190398099483763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404193368253864132645017 2553145026190398099483763)
            ·
              refine ⟨3829717539285597149225645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553145026190398099483763 3829717539285597149225645)
              ·
                refine ⟨1436144077232098930959617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3829717539285597149225645 1436144077232098930959617)
                ·
                  refine ⟨1077108057924074198219713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436144077232098930959617 1077108057924074198219713)
                  ·
                    refine ⟨807831043443055648664785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077108057924074198219713 807831043443055648664785)
                    ·
                      refine ⟨605873282582291736498589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807831043443055648664785 605873282582291736498589)
                      ·
                        rfl

theorem cell23_1179934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1179934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179934 prefixEnd_1179934 := by exact prefixLift 1179934
  have htrace : WordTrace (prefixWord ++ tailWord_1179934) baseStart_1179934 baseEnd_1179934 := by
    simpa [prefixWord, tailWord_1179934, baseEnd_1179934] using wordTrace_append hprefix tailTrace_1179934
  have hstable : (prefixWord ++ tailWord_1179934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179934).length < 2 ^ (prefixWord ++ tailWord_1179934).sum := by decide
  have hdescent : baseEnd_1179934 < baseStart_1179934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179953 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_1179953 : Nat := 118140960795 + 1179953 * 2 ^ 59
def prefixEnd_1179953 : Nat := 4983230072969 + 3 ^ 40 * 1179953 * 2
def baseEnd_1179953 : Nat := 201961012904909054053667

theorem tailTrace_1179953 : CollatzResearch.WordTrace tailWord_1179953 prefixEnd_1179953 201961012904909054053667 := by
  unfold tailWord_1179953
  simp only [CollatzResearch.WordTrace]
  refine ⟨43036421494239275773688513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28690947662826183849125675 43036421494239275773688513)
  ·
    refine ⟨32277316120679456830266385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43036421494239275773688513 32277316120679456830266385)
    ·
      refine ⟨24207987090509592622699789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32277316120679456830266385 24207987090509592622699789)
      ·
        refine ⟨9077995158941097233512421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24207987090509592622699789 9077995158941097233512421)
        ·
          refine ⟨1702124092301455731283579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9077995158941097233512421 1702124092301455731283579)
          ·
            refine ⟨2553186138452183596925369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702124092301455731283579 2553186138452183596925369)
            ·
              refine ⟨1914889603839137697694027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553186138452183596925369 1914889603839137697694027)
              ·
                refine ⟨2872334405758706546541041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914889603839137697694027 2872334405758706546541041)
                ·
                  refine ⟨2154250804319029909905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872334405758706546541041 2154250804319029909905781)
                  ·
                    refine ⟨201961012904909054053667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2154250804319029909905781 201961012904909054053667)
                    ·
                      rfl

theorem cell23_1179953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_1179953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1179953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1179953 prefixEnd_1179953 := by exact prefixLift 1179953
  have htrace : WordTrace (prefixWord ++ tailWord_1179953) baseStart_1179953 baseEnd_1179953 := by
    simpa [prefixWord, tailWord_1179953, baseEnd_1179953] using wordTrace_append hprefix tailTrace_1179953
  have hstable : (prefixWord ++ tailWord_1179953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179953).length < 2 ^ (prefixWord ++ tailWord_1179953).sum := by decide
  have hdescent : baseEnd_1179953 < baseStart_1179953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180010 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1180010 : Nat := 118140960795 + 1180010 * 2 ^ 59
def prefixEnd_1180010 : Nat := 4983230072969 + 3 ^ 40 * 1180010 * 2
def baseEnd_1180010 : Nat := 605912307112033439148239

theorem tailTrace_1180010 : CollatzResearch.WordTrace tailWord_1180010 prefixEnd_1180010 605912307112033439148239 := by
  unfold tailWord_1180010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10759625113758193627128371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28692333636688516339008989 10759625113758193627128371)
  ·
    refine ⟨16139437670637290440692557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10759625113758193627128371 16139437670637290440692557)
    ·
      refine ⟨6052289126488983915259709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16139437670637290440692557 6052289126488983915259709)
      ·
        refine ⟨2269608422433368968222391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6052289126488983915259709 2269608422433368968222391)
        ·
          refine ⟨3404412633650053452333587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269608422433368968222391 3404412633650053452333587)
          ·
            refine ⟨5106618950475080178500381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404412633650053452333587 5106618950475080178500381)
            ·
              refine ⟨1914982106428155066937643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5106618950475080178500381 1914982106428155066937643)
              ·
                refine ⟨2872473159642232600406465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914982106428155066937643 2872473159642232600406465)
                ·
                  refine ⟨2154354869731674450304849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872473159642232600406465 2154354869731674450304849)
                  ·
                    refine ⟨1615766152298755837728637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2154354869731674450304849 1615766152298755837728637)
                    ·
                      refine ⟨605912307112033439148239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615766152298755837728637 605912307112033439148239)
                      ·
                        rfl

theorem cell23_1180010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1180010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180010 prefixEnd_1180010 := by exact prefixLift 1180010
  have htrace : WordTrace (prefixWord ++ tailWord_1180010) baseStart_1180010 baseEnd_1180010 := by
    simpa [prefixWord, tailWord_1180010, baseEnd_1180010] using wordTrace_append hprefix tailTrace_1180010
  have hstable : (prefixWord ++ tailWord_1180010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180010).length < 2 ^ (prefixWord ++ tailWord_1180010).sum := by decide
  have hdescent : baseEnd_1180010 < baseStart_1180010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180019 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_1180019 : Nat := 118140960795 + 1180019 * 2 ^ 59
def prefixEnd_1180019 : Nat := 4983230072969 + 3 ^ 40 * 1180019 * 2
def baseEnd_1180019 : Nat := 605916928437923903935697

theorem tailTrace_1180019 : CollatzResearch.WordTrace tailWord_1180019 prefixEnd_1180019 605916928437923903935697 := by
  unfold tailWord_1180019
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038828712000169045591111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28692552474666779363727407 43038828712000169045591111)
  ·
    refine ⟨64558243068000253568386667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43038828712000169045591111 64558243068000253568386667)
    ·
      refine ⟨96837364602000380352580001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64558243068000253568386667 96837364602000380352580001)
      ·
        refine ⟨72628023451500285264435001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96837364602000380352580001 72628023451500285264435001)
        ·
          refine ⟨54471017588625213948326251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72628023451500285264435001 54471017588625213948326251)
          ·
            refine ⟨81706526382937820922489377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54471017588625213948326251 81706526382937820922489377)
            ·
              refine ⟨61279894787203365691867033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81706526382937820922489377 61279894787203365691867033)
              ·
                refine ⟨45959921090402524268900275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61279894787203365691867033 45959921090402524268900275)
                ·
                  refine ⟨68939881635603786403350413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45959921090402524268900275 68939881635603786403350413)
                  ·
                    refine ⟨25852455613351419901256405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68939881635603786403350413 25852455613351419901256405)
                    ·
                      refine ⟨605916928437923903935697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25852455613351419901256405 605916928437923903935697)
                      ·
                        rfl

theorem cell23_1180019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_1180019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180019 prefixEnd_1180019 := by exact prefixLift 1180019
  have htrace : WordTrace (prefixWord ++ tailWord_1180019) baseStart_1180019 baseEnd_1180019 := by
    simpa [prefixWord, tailWord_1180019, baseEnd_1180019] using wordTrace_append hprefix tailTrace_1180019
  have hstable : (prefixWord ++ tailWord_1180019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180019).length < 2 ^ (prefixWord ++ tailWord_1180019).sum := by decide
  have hdescent : baseEnd_1180019 < baseStart_1180019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180040 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1180040 : Nat := 118140960795 + 1180040 * 2 ^ 59
def prefixEnd_1180040 : Nat := 4983230072969 + 3 ^ 40 * 1180040 * 2
def baseEnd_1180040 : Nat := 605927711531668321773101

theorem tailTrace_1180040 : CollatzResearch.WordTrace tailWord_1180040 prefixEnd_1180040 605927711531668321773101 := by
  unfold tailWord_1180040
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519797322462044816052787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28693063096616059754737049 21519797322462044816052787)
  ·
    refine ⟨32279695983693067224079181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21519797322462044816052787 32279695983693067224079181)
    ·
      refine ⟨12104885993884900209029693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32279695983693067224079181 12104885993884900209029693)
      ·
        refine ⟨4539332247706837578386135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12104885993884900209029693 4539332247706837578386135)
        ·
          refine ⟨6808998371560256367579203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539332247706837578386135 6808998371560256367579203)
          ·
            refine ⟨10213497557340384551368805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808998371560256367579203 10213497557340384551368805)
            ·
              refine ⟨1915030792001322103381651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10213497557340384551368805 1915030792001322103381651)
              ·
                refine ⟨2872546188001983155072477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915030792001322103381651 2872546188001983155072477)
                ·
                  refine ⟨1077204820500743683152179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2872546188001983155072477 1077204820500743683152179)
                  ·
                    refine ⟨1615807230751115524728269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077204820500743683152179 1615807230751115524728269)
                    ·
                      refine ⟨605927711531668321773101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615807230751115524728269 605927711531668321773101)
                      ·
                        rfl

theorem cell23_1180040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1180040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180040 prefixEnd_1180040 := by exact prefixLift 1180040
  have htrace : WordTrace (prefixWord ++ tailWord_1180040) baseStart_1180040 baseEnd_1180040 := by
    simpa [prefixWord, tailWord_1180040, baseEnd_1180040] using wordTrace_append hprefix tailTrace_1180040
  have hstable : (prefixWord ++ tailWord_1180040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180040).length < 2 ^ (prefixWord ++ tailWord_1180040).sum := by decide
  have hdescent : baseEnd_1180040 < baseStart_1180040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180063 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1180063 : Nat := 118140960795 + 1180063 * 2 ^ 59
def prefixEnd_1180063 : Nat := 4983230072969 + 3 ^ 40 * 1180063 * 2
def baseEnd_1180063 : Nat := 605939521586721731785495

theorem tailTrace_1180063 : CollatzResearch.WordTrace tailWord_1180063 prefixEnd_1180063 605939521586721731785495 := by
  unfold tailWord_1180063
  simp only [CollatzResearch.WordTrace]
  refine ⟨43040433523840764560192843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28693622349227176373461895 43040433523840764560192843)
  ·
    refine ⟨64560650285761146840289265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43040433523840764560192843 64560650285761146840289265)
    ·
      refine ⟨48420487714320860130216949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64560650285761146840289265 48420487714320860130216949)
      ·
        refine ⟨4539420723217580637207839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48420487714320860130216949 4539420723217580637207839)
        ·
          refine ⟨6809131084826370955811759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539420723217580637207839 6809131084826370955811759)
          ·
            refine ⟨10213696627239556433717639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809131084826370955811759 10213696627239556433717639)
            ·
              refine ⟨15320544940859334650576459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213696627239556433717639 15320544940859334650576459)
              ·
                refine ⟨22980817411289001975864689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15320544940859334650576459 22980817411289001975864689)
                ·
                  refine ⟨17235613058466751481898517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22980817411289001975864689 17235613058466751481898517)
                  ·
                    refine ⟨807919362115628975713993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17235613058466751481898517 807919362115628975713993)
                    ·
                      refine ⟨605939521586721731785495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 807919362115628975713993 605939521586721731785495)
                      ·
                        rfl

theorem cell23_1180063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1180063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180063 prefixEnd_1180063 := by exact prefixLift 1180063
  have htrace : WordTrace (prefixWord ++ tailWord_1180063) baseStart_1180063 baseEnd_1180063 := by
    simpa [prefixWord, tailWord_1180063, baseEnd_1180063] using wordTrace_append hprefix tailTrace_1180063
  have hstable : (prefixWord ++ tailWord_1180063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180063).length < 2 ^ (prefixWord ++ tailWord_1180063).sum := by decide
  have hdescent : baseEnd_1180063 < baseStart_1180063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180076 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1180076 : Nat := 118140960795 + 1180076 * 2 ^ 59
def prefixEnd_1180076 : Nat := 4983230072969 + 3 ^ 40 * 1180076 * 2
def baseEnd_1180076 : Nat := 605946196835230180922935

theorem tailTrace_1180076 : CollatzResearch.WordTrace tailWord_1180076 prefixEnd_1180076 605946196835230180922935 := by
  unfold tailWord_1180076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21520453836396833890208041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28693938448529111853610721 21520453836396833890208041)
  ·
    refine ⟨16140340377297625417656031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21520453836396833890208041 16140340377297625417656031)
    ·
      refine ⟨24210510565946438126484047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16140340377297625417656031 24210510565946438126484047)
      ·
        refine ⟨36315765848919657189726071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24210510565946438126484047 36315765848919657189726071)
        ·
          refine ⟨54473648773379485784589107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36315765848919657189726071 54473648773379485784589107)
          ·
            refine ⟨81710473160069228676883661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54473648773379485784589107 81710473160069228676883661)
            ·
              refine ⟨30641427435025960753831373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81710473160069228676883661 30641427435025960753831373)
              ·
                refine ⟨11490535288134735282686765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30641427435025960753831373 11490535288134735282686765)
                ·
                  refine ⟨4308950733050525731007537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11490535288134735282686765 4308950733050525731007537)
                  ·
                    refine ⟨3231713049787894298255653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4308950733050525731007537 3231713049787894298255653)
                    ·
                      refine ⟨605946196835230180922935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3231713049787894298255653 605946196835230180922935)
                      ·
                        rfl

theorem cell23_1180076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1180076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180076 prefixEnd_1180076 := by exact prefixLift 1180076
  have htrace : WordTrace (prefixWord ++ tailWord_1180076) baseStart_1180076 baseEnd_1180076 := by
    simpa [prefixWord, tailWord_1180076, baseEnd_1180076] using wordTrace_append hprefix tailTrace_1180076
  have hstable : (prefixWord ++ tailWord_1180076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180076).length < 2 ^ (prefixWord ++ tailWord_1180076).sum := by decide
  have hdescent : baseEnd_1180076 < baseStart_1180076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180106 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1180106 : Nat := 118140960795 + 1180106 * 2 ^ 59
def prefixEnd_1180106 : Nat := 4983230072969 + 3 ^ 40 * 1180106 * 2
def baseEnd_1180106 : Nat := 605961601254865063547797

theorem tailTrace_1180106 : CollatzResearch.WordTrace tailWord_1180106 prefixEnd_1180106 605961601254865063547797 := by
  unfold tailWord_1180106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760500465671245726002043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28694667908456655269338781 10760500465671245726002043)
  ·
    refine ⟨16140750698506868589003065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10760500465671245726002043 16140750698506868589003065)
    ·
      refine ⟨12105563023880151441752299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16140750698506868589003065 12105563023880151441752299)
      ·
        refine ⟨18158344535820227162628449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105563023880151441752299 18158344535820227162628449)
        ·
          refine ⟨13618758401865170371971337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18158344535820227162628449 13618758401865170371971337)
          ·
            refine ⟨10214068801398877778978503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13618758401865170371971337 10214068801398877778978503)
            ·
              refine ⟨15321103202098316668467755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10214068801398877778978503 15321103202098316668467755)
              ·
                refine ⟨22981654803147475002701633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15321103202098316668467755 22981654803147475002701633)
                ·
                  refine ⟨17236241102360606252026225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22981654803147475002701633 17236241102360606252026225)
                  ·
                    refine ⟨12927180826770454689019669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17236241102360606252026225 12927180826770454689019669)
                    ·
                      refine ⟨605961601254865063547797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12927180826770454689019669 605961601254865063547797)
                      ·
                        rfl

theorem cell23_1180106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1180106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180106 prefixEnd_1180106 := by exact prefixLift 1180106
  have htrace : WordTrace (prefixWord ++ tailWord_1180106) baseStart_1180106 baseEnd_1180106 := by
    simpa [prefixWord, tailWord_1180106, baseEnd_1180106] using wordTrace_append hprefix tailTrace_1180106
  have hstable : (prefixWord ++ tailWord_1180106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180106).length < 2 ^ (prefixWord ++ tailWord_1180106).sum := by decide
  have hdescent : baseEnd_1180106 < baseStart_1180106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180114 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1180114 : Nat := 118140960795 + 1180114 * 2 ^ 59
def prefixEnd_1180114 : Nat := 4983230072969 + 3 ^ 40 * 1180114 * 2
def baseEnd_1180114 : Nat := 605965709100101032247761

theorem tailTrace_1180114 : CollatzResearch.WordTrace tailWord_1180114 prefixEnd_1180114 605965709100101032247761 := by
  unfold tailWord_1180114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760573411664000067574849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28694862431104000180199597 10760573411664000067574849)
  ·
    refine ⟨8070430058748000050681137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10760573411664000067574849 8070430058748000050681137)
    ·
      refine ⟨6052822544061000038010853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070430058748000050681137 6052822544061000038010853)
      ·
        refine ⟨1134904227011437507127035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6052822544061000038010853 1134904227011437507127035)
        ·
          refine ⟨1702356340517156260690553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134904227011437507127035 1702356340517156260690553)
          ·
            refine ⟨1276767255387867195517915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702356340517156260690553 1276767255387867195517915)
            ·
              refine ⟨1915150883081800793276873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276767255387867195517915 1915150883081800793276873)
              ·
                refine ⟨1436363162311350594957655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915150883081800793276873 1436363162311350594957655)
                ·
                  refine ⟨2154544743467025892436483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436363162311350594957655 2154544743467025892436483)
                  ·
                    refine ⟨3231817115200538838654725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154544743467025892436483 3231817115200538838654725)
                    ·
                      refine ⟨605965709100101032247761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3231817115200538838654725 605965709100101032247761)
                      ·
                        rfl

theorem cell23_1180114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1180114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180114 prefixEnd_1180114 := by exact prefixLift 1180114
  have htrace : WordTrace (prefixWord ++ tailWord_1180114) baseStart_1180114 baseEnd_1180114 := by
    simpa [prefixWord, tailWord_1180114, baseEnd_1180114] using wordTrace_append hprefix tailTrace_1180114
  have hstable : (prefixWord ++ tailWord_1180114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180114).length < 2 ^ (prefixWord ++ tailWord_1180114).sum := by decide
  have hdescent : baseEnd_1180114 < baseStart_1180114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180117 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1180117 : Nat := 118140960795 + 1180117 * 2 ^ 59
def prefixEnd_1180117 : Nat := 4983230072969 + 3 ^ 40 * 1180117 * 2
def baseEnd_1180117 : Nat := 605967249542064520510247

theorem tailTrace_1180117 : CollatzResearch.WordTrace tailWord_1180117 prefixEnd_1180117 605967249542064520510247 := by
  unfold tailWord_1180117
  simp only [CollatzResearch.WordTrace]
  refine ⟨43042403065645131782658605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28694935377096754521772403 43042403065645131782658605)
  ·
    refine ⟨16140901149616924418496977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43042403065645131782658605 16140901149616924418496977)
    ·
      refine ⟨12105675862212693313872733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16140901149616924418496977 12105675862212693313872733)
      ·
        refine ⟨4539628448329759992702275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12105675862212693313872733 4539628448329759992702275)
        ·
          refine ⟨6809442672494639989053413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539628448329759992702275 6809442672494639989053413)
          ·
            refine ⟨1276770501092744997947515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6809442672494639989053413 1276770501092744997947515)
            ·
              refine ⟨1915155751639117496921273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276770501092744997947515 1915155751639117496921273)
              ·
                refine ⟨1436366813729338122690955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915155751639117496921273 1436366813729338122690955)
                ·
                  refine ⟨2154550220594007184036433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436366813729338122690955 2154550220594007184036433)
                  ·
                    refine ⟨1615912665445505388027325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2154550220594007184036433 1615912665445505388027325)
                    ·
                      refine ⟨605967249542064520510247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1615912665445505388027325 605967249542064520510247)
                      ·
                        rfl

theorem cell23_1180117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1180117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180117 prefixEnd_1180117 := by exact prefixLift 1180117
  have htrace : WordTrace (prefixWord ++ tailWord_1180117) baseStart_1180117 baseEnd_1180117 := by
    simpa [prefixWord, tailWord_1180117, baseEnd_1180117] using wordTrace_append hprefix tailTrace_1180117
  have hstable : (prefixWord ++ tailWord_1180117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180117).length < 2 ^ (prefixWord ++ tailWord_1180117).sum := by decide
  have hdescent : baseEnd_1180117 < baseStart_1180117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180200 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1180200 : Nat := 118140960795 + 1180200 * 2 ^ 59
def prefixEnd_1180200 : Nat := 4983230072969 + 3 ^ 40 * 1180200 * 2
def baseEnd_1180200 : Nat := 606009868436387695772365

theorem tailTrace_1180200 : CollatzResearch.WordTrace tailWord_1180200 prefixEnd_1180200 606009868436387695772365 := by
  unfold tailWord_1180200
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522715162172218478965027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28696953549562957971953369 21522715162172218478965027)
  ·
    refine ⟨32284072743258327718447541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21522715162172218478965027 32284072743258327718447541)
    ·
      refine ⟨3026631819680468223604457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32284072743258327718447541 3026631819680468223604457)
      ·
        refine ⟨2269973864760351167703343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3026631819680468223604457 2269973864760351167703343)
        ·
          refine ⟨3404960797140526751555015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269973864760351167703343 3404960797140526751555015)
          ·
            refine ⟨5107441195710790127332523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404960797140526751555015 5107441195710790127332523)
            ·
              refine ⟨7661161793566185190998785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107441195710790127332523 7661161793566185190998785)
              ·
                refine ⟨5745871345174638893249089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661161793566185190998785 5745871345174638893249089)
                ·
                  refine ⟨4309403508880979169936817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745871345174638893249089 4309403508880979169936817)
                  ·
                    refine ⟨3232052631660734377452613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309403508880979169936817 3232052631660734377452613)
                    ·
                      refine ⟨606009868436387695772365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3232052631660734377452613 606009868436387695772365)
                      ·
                        rfl

theorem cell23_1180200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1180200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180200 prefixEnd_1180200 := by exact prefixLift 1180200
  have htrace : WordTrace (prefixWord ++ tailWord_1180200) baseStart_1180200 baseEnd_1180200 := by
    simpa [prefixWord, tailWord_1180200, baseEnd_1180200] using wordTrace_append hprefix tailTrace_1180200
  have hstable : (prefixWord ++ tailWord_1180200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180200).length < 2 ^ (prefixWord ++ tailWord_1180200).sum := by decide
  have hdescent : baseEnd_1180200 < baseStart_1180200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180210 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_1180210 : Nat := 118140960795 + 1180210 * 2 ^ 59
def prefixEnd_1180210 : Nat := 4983230072969 + 3 ^ 40 * 1180210 * 2
def baseEnd_1180210 : Nat := 67335000360325850738591

theorem tailTrace_1180210 : CollatzResearch.WordTrace tailWord_1180210 prefixEnd_1180210 67335000360325850738591 := by
  unfold tailWord_1180210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761448763577052166448521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28697196702872139110529389 10761448763577052166448521)
  ·
    refine ⟨8071086572682789124836391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10761448763577052166448521 8071086572682789124836391)
    ·
      refine ⟨12106629859024183687254587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071086572682789124836391 12106629859024183687254587)
      ·
        refine ⟨18159944788536275530881881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12106629859024183687254587 18159944788536275530881881)
        ·
          refine ⟨13619958591402206648161411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18159944788536275530881881 13619958591402206648161411)
          ·
            refine ⟨20429937887103309972242117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13619958591402206648161411 20429937887103309972242117)
            ·
              refine ⟨3830613353831870619795397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20429937887103309972242117 3830613353831870619795397)
              ·
                refine ⟨718240003843475741211637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3830613353831870619795397 718240003843475741211637)
                ·
                  refine ⟨67335000360325850738591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 718240003843475741211637 67335000360325850738591)
                  ·
                    rfl

theorem cell23_1180210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_1180210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180210 prefixEnd_1180210 := by exact prefixLift 1180210
  have htrace : WordTrace (prefixWord ++ tailWord_1180210) baseStart_1180210 baseEnd_1180210 := by
    simpa [prefixWord, tailWord_1180210, baseEnd_1180210] using wordTrace_append hprefix tailTrace_1180210
  have hstable : (prefixWord ++ tailWord_1180210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180210).length < 2 ^ (prefixWord ++ tailWord_1180210).sum := by decide
  have hdescent : baseEnd_1180210 < baseStart_1180210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180220 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_1180220 : Nat := 118140960795 + 1180220 * 2 ^ 59
def prefixEnd_1180220 : Nat := 4983230072969 + 3 ^ 40 * 1180220 * 2
def baseEnd_1180220 : Nat := 606020138049477617522273

theorem tailTrace_1180220 : CollatzResearch.WordTrace tailWord_1180220 prefixEnd_1180220 606020138049477617522273 := by
  unfold tailWord_1180220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21523079892135990186829057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28697439856181320249105409 21523079892135990186829057)
  ·
    refine ⟨16142309919101992640121793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21523079892135990186829057 16142309919101992640121793)
    ·
      refine ⟨12106732439326494480091345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16142309919101992640121793 12106732439326494480091345)
      ·
        refine ⟨9080049329494870860068509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12106732439326494480091345 9080049329494870860068509)
        ·
          refine ⟨3405018498560576572525691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9080049329494870860068509 3405018498560576572525691)
          ·
            refine ⟨5107527747840864858788537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405018498560576572525691 5107527747840864858788537)
            ·
              refine ⟨3830645810880648644091403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107527747840864858788537 3830645810880648644091403)
              ·
                refine ⟨5745968716320972966137105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830645810880648644091403 5745968716320972966137105)
                ·
                  refine ⟨4309476537240729724602829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745968716320972966137105 4309476537240729724602829)
                  ·
                    refine ⟨1616053701465273646726061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4309476537240729724602829 1616053701465273646726061)
                    ·
                      refine ⟨606020138049477617522273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1616053701465273646726061 606020138049477617522273)
                      ·
                        rfl

theorem cell23_1180220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_1180220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180220 prefixEnd_1180220 := by exact prefixLift 1180220
  have htrace : WordTrace (prefixWord ++ tailWord_1180220) baseStart_1180220 baseEnd_1180220 := by
    simpa [prefixWord, tailWord_1180220, baseEnd_1180220] using wordTrace_append hprefix tailTrace_1180220
  have hstable : (prefixWord ++ tailWord_1180220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180220).length < 2 ^ (prefixWord ++ tailWord_1180220).sum := by decide
  have hdescent : baseEnd_1180220 < baseStart_1180220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180221 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_1180221 : Nat := 118140960795 + 1180221 * 2 ^ 59
def prefixEnd_1180221 : Nat := 4983230072969 + 3 ^ 40 * 1180221 * 2
def baseEnd_1180221 : Nat := 606020651530132113609769

theorem tailTrace_1180221 : CollatzResearch.WordTrace tailWord_1180221 prefixEnd_1180221 606020651530132113609769 := by
  unfold tailWord_1180221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046196257268357544444517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28697464171512238362963011 43046196257268357544444517)
  ·
    refine ⟨8071161798237817039583347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43046196257268357544444517 8071161798237817039583347)
    ·
      refine ⟨12106742697356725559375021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071161798237817039583347 12106742697356725559375021)
      ·
        refine ⟨4540028511508772084765633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12106742697356725559375021 4540028511508772084765633)
        ·
          refine ⟨3405021383631579063574225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540028511508772084765633 3405021383631579063574225)
          ·
            refine ⟨2553766037723684297680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405021383631579063574225 2553766037723684297680669)
            ·
              refine ⟨957662264146381611630251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2553766037723684297680669 957662264146381611630251)
              ·
                refine ⟨1436493396219572417445377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957662264146381611630251 1436493396219572417445377)
                ·
                  refine ⟨1077370047164679313084033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436493396219572417445377 1077370047164679313084033)
                  ·
                    refine ⟨808027535373509484813025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077370047164679313084033 808027535373509484813025)
                    ·
                      refine ⟨606020651530132113609769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808027535373509484813025 606020651530132113609769)
                      ·
                        rfl

theorem cell23_1180221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_1180221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180221 prefixEnd_1180221 := by exact prefixLift 1180221
  have htrace : WordTrace (prefixWord ++ tailWord_1180221) baseStart_1180221 baseEnd_1180221 := by
    simpa [prefixWord, tailWord_1180221, baseEnd_1180221] using wordTrace_append hprefix tailTrace_1180221
  have hstable : (prefixWord ++ tailWord_1180221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180221).length < 2 ^ (prefixWord ++ tailWord_1180221).sum := by decide
  have hdescent : baseEnd_1180221 < baseStart_1180221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180260 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1180260 : Nat := 118140960795 + 1180260 * 2 ^ 59
def prefixEnd_1180260 : Nat := 4983230072969 + 3 ^ 40 * 1180260 * 2
def baseEnd_1180260 : Nat := 606040677275657461022089

theorem tailTrace_1180260 : CollatzResearch.WordTrace tailWord_1180260 prefixEnd_1180260 606040677275657461022089 := by
  unfold tailWord_1180260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21523809352063533602557117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28698412469418044803409489 21523809352063533602557117)
  ·
    refine ⟨8071428507023825100958919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21523809352063533602557117 8071428507023825100958919)
    ·
      refine ⟨12107142760535737651438379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071428507023825100958919 12107142760535737651438379)
      ·
        refine ⟨18160714140803606477157569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12107142760535737651438379 18160714140803606477157569)
        ·
          refine ⟨13620535605602704857868177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18160714140803606477157569 13620535605602704857868177)
          ·
            refine ⟨10215401704202028643401133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13620535605602704857868177 10215401704202028643401133)
            ·
              refine ⟨3830775639075760741275425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10215401704202028643401133 3830775639075760741275425)
              ·
                refine ⟨2873081729306820555956569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830775639075760741275425 2873081729306820555956569)
                ·
                  refine ⟨2154811296980115416967427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873081729306820555956569 2154811296980115416967427)
                  ·
                    refine ⟨3232216945470173125451141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154811296980115416967427 3232216945470173125451141)
                    ·
                      refine ⟨606040677275657461022089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3232216945470173125451141 606040677275657461022089)
                      ·
                        rfl

theorem cell23_1180260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1180260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180260 prefixEnd_1180260 := by exact prefixLift 1180260
  have htrace : WordTrace (prefixWord ++ tailWord_1180260) baseStart_1180260 baseEnd_1180260 := by
    simpa [prefixWord, tailWord_1180260, baseEnd_1180260] using wordTrace_append hprefix tailTrace_1180260
  have hstable : (prefixWord ++ tailWord_1180260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180260).length < 2 ^ (prefixWord ++ tailWord_1180260).sum := by decide
  have hdescent : baseEnd_1180260 < baseStart_1180260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180360 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1180360 : Nat := 118140960795 + 1180360 * 2 ^ 59
def prefixEnd_1180360 : Nat := 4983230072969 + 3 ^ 40 * 1180360 * 2
def baseEnd_1180360 : Nat := 202030675113702356590543

theorem tailTrace_1180360 : CollatzResearch.WordTrace tailWord_1180360 prefixEnd_1180360 202030675113702356590543 := by
  unfold tailWord_1180360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525633001882392141877267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28700844002509856189169689 21525633001882392141877267)
  ·
    refine ⟨32288449502823588212815901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21525633001882392141877267 32288449502823588212815901)
    ·
      refine ⟨12108168563558845579805963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32288449502823588212815901 12108168563558845579805963)
      ·
        refine ⟨18162252845338268369708945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12108168563558845579805963 18162252845338268369708945)
        ·
          refine ⟨13621689634003701277281709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18162252845338268369708945 13621689634003701277281709)
          ·
            refine ⟨5108133612751387978980641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13621689634003701277281709 5108133612751387978980641)
            ·
              refine ⟨3831100209563540984235481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108133612751387978980641 3831100209563540984235481)
              ·
                refine ⟨2873325157172655738176611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831100209563540984235481 2873325157172655738176611)
                ·
                  refine ⟨4309987735758983607264917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873325157172655738176611 4309987735758983607264917)
                  ·
                    refine ⟨202030675113702356590543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4309987735758983607264917 202030675113702356590543)
                    ·
                      rfl

theorem cell23_1180360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1180360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180360 prefixEnd_1180360 := by exact prefixLift 1180360
  have htrace : WordTrace (prefixWord ++ tailWord_1180360) baseStart_1180360 baseEnd_1180360 := by
    simpa [prefixWord, tailWord_1180360, baseEnd_1180360] using wordTrace_append hprefix tailTrace_1180360
  have hstable : (prefixWord ++ tailWord_1180360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180360).length < 2 ^ (prefixWord ++ tailWord_1180360).sum := by decide
  have hdescent : baseEnd_1180360 < baseStart_1180360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180363 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_1180363 : Nat := 118140960795 + 1180363 * 2 ^ 59
def prefixEnd_1180363 : Nat := 4983230072969 + 3 ^ 40 * 1180363 * 2
def baseEnd_1180363 : Nat := 606093565783070558034115

theorem tailTrace_1180363 : CollatzResearch.WordTrace tailWord_1180363 prefixEnd_1180363 606093565783070558034115 := by
  unfold tailWord_1180363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43051375422753915796113743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28700916948502610530742495 43051375422753915796113743)
  ·
    refine ⟨64577063134130873694170615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43051375422753915796113743 64577063134130873694170615)
    ·
      refine ⟨96865594701196310541255923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64577063134130873694170615 96865594701196310541255923)
      ·
        refine ⟨145298392051794465811883885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96865594701196310541255923 145298392051794465811883885)
        ·
          refine ⟨54486897019422924679456457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145298392051794465811883885 54486897019422924679456457)
          ·
            refine ⟨40865172764567193509592343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54486897019422924679456457 40865172764567193509592343)
            ·
              refine ⟨61297759146850790264388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40865172764567193509592343 61297759146850790264388515)
              ·
                refine ⟨91946638720276185396582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61297759146850790264388515 91946638720276185396582773)
                ·
                  refine ⟨8619997380025892380929635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91946638720276185396582773 8619997380025892380929635)
                  ·
                    refine ⟨12929996070038838571394453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8619997380025892380929635 12929996070038838571394453)
                    ·
                      refine ⟨606093565783070558034115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12929996070038838571394453 606093565783070558034115)
                      ·
                        rfl

theorem cell23_1180363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_1180363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180363 prefixEnd_1180363 := by exact prefixLift 1180363
  have htrace : WordTrace (prefixWord ++ tailWord_1180363) baseStart_1180363 baseEnd_1180363 := by
    simpa [prefixWord, tailWord_1180363, baseEnd_1180363] using wordTrace_append hprefix tailTrace_1180363
  have hstable : (prefixWord ++ tailWord_1180363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180363).length < 2 ^ (prefixWord ++ tailWord_1180363).sum := by decide
  have hdescent : baseEnd_1180363 < baseStart_1180363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180364 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_1180364 : Nat := 118140960795 + 1180364 * 2 ^ 59
def prefixEnd_1180364 : Nat := 4983230072969 + 3 ^ 40 * 1180364 * 2
def baseEnd_1180364 : Nat := 202031359754575018040537

theorem tailTrace_1180364 : CollatzResearch.WordTrace tailWord_1180364 prefixEnd_1180364 202031359754575018040537 := by
  unfold tailWord_1180364
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525705947875146483450073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28700941263833528644600097 21525705947875146483450073)
  ·
    refine ⟨16144279460906359862587555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21525705947875146483450073 16144279460906359862587555)
    ·
      refine ⟨24216419191359539793881333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16144279460906359862587555 24216419191359539793881333)
      ·
        refine ⟨2270289299189956855676375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24216419191359539793881333 2270289299189956855676375)
        ·
          refine ⟨3405433948784935283514563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270289299189956855676375 3405433948784935283514563)
          ·
            refine ⟨5108150923177402925271845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405433948784935283514563 5108150923177402925271845)
            ·
              refine ⟨957778298095763048488471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5108150923177402925271845 957778298095763048488471)
              ·
                refine ⟨1436667447143644572732707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957778298095763048488471 1436667447143644572732707)
                ·
                  refine ⟨2155001170715466859099061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436667447143644572732707 2155001170715466859099061)
                  ·
                    refine ⟨202031359754575018040537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2155001170715466859099061 202031359754575018040537)
                    ·
                      rfl

theorem cell23_1180364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_1180364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180364 prefixEnd_1180364 := by exact prefixLift 1180364
  have htrace : WordTrace (prefixWord ++ tailWord_1180364) baseStart_1180364 baseEnd_1180364 := by
    simpa [prefixWord, tailWord_1180364, baseEnd_1180364] using wordTrace_append hprefix tailTrace_1180364
  have hstable : (prefixWord ++ tailWord_1180364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180364).length < 2 ^ (prefixWord ++ tailWord_1180364).sum := by decide
  have hdescent : baseEnd_1180364 < baseStart_1180364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180387 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1180387 : Nat := 118140960795 + 1180387 * 2 ^ 59
def prefixEnd_1180387 : Nat := 4983230072969 + 3 ^ 40 * 1180387 * 2
def baseEnd_1180387 : Nat := 606105889318778464134005

theorem tailTrace_1180387 : CollatzResearch.WordTrace tailWord_1180387 prefixEnd_1180387 606105889318778464134005 := by
  unfold tailWord_1180387
  simp only [CollatzResearch.WordTrace]
  refine ⟨43052250774666967894987415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28701500516444645263324943 43052250774666967894987415)
  ·
    refine ⟨64578376162000451842481123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43052250774666967894987415 64578376162000451842481123)
    ·
      refine ⟨96867564243000677763721685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64578376162000451842481123 96867564243000677763721685)
      ·
        refine ⟨2270333536945328385087227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96867564243000677763721685 2270333536945328385087227)
        ·
          refine ⟨3405500305417992577630841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270333536945328385087227 3405500305417992577630841)
          ·
            refine ⟨2554125229063494433223131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405500305417992577630841 2554125229063494433223131)
            ·
              refine ⟨3831187843595241649834697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554125229063494433223131 3831187843595241649834697)
              ·
                refine ⟨2873390882696431237376023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831187843595241649834697 2873390882696431237376023)
                ·
                  refine ⟨4310086324044646856064035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873390882696431237376023 4310086324044646856064035)
                  ·
                    refine ⟨6465129486066970284096053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4310086324044646856064035 6465129486066970284096053)
                    ·
                      refine ⟨606105889318778464134005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6465129486066970284096053 606105889318778464134005)
                      ·
                        rfl

theorem cell23_1180387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1180387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180387 prefixEnd_1180387 := by exact prefixLift 1180387
  have htrace : WordTrace (prefixWord ++ tailWord_1180387) baseStart_1180387 baseEnd_1180387 := by
    simpa [prefixWord, tailWord_1180387, baseEnd_1180387] using wordTrace_append hprefix tailTrace_1180387
  have hstable : (prefixWord ++ tailWord_1180387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180387).length < 2 ^ (prefixWord ++ tailWord_1180387).sum := by decide
  have hdescent : baseEnd_1180387 < baseStart_1180387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180427 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 5, 3, 2]
def baseStart_1180427 : Nat := 118140960795 + 1180427 * 2 ^ 59
def prefixEnd_1180427 : Nat := 4983230072969 + 3 ^ 40 * 1180427 * 2
def baseEnd_1180427 : Nat := 606126428544958307633821

theorem tailTrace_1180427 : CollatzResearch.WordTrace tailWord_1180427 prefixEnd_1180427 606126428544958307633821 := by
  unfold tailWord_1180427
  simp only [CollatzResearch.WordTrace]
  refine ⟨43053709694522054726443535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28702473129681369817629023 43053709694522054726443535)
  ·
    refine ⟨64580564541783082089665303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43053709694522054726443535 64580564541783082089665303)
    ·
      refine ⟨96870846812674623134497955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64580564541783082089665303 96870846812674623134497955)
      ·
        refine ⟨145306270219011934701746933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96870846812674623134497955 145306270219011934701746933)
        ·
          refine ⟨13622462833032368878288775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145306270219011934701746933 13622462833032368878288775)
          ·
            refine ⟨20433694249548553317433163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13622462833032368878288775 20433694249548553317433163)
            ·
              refine ⟨30650541374322829976149745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20433694249548553317433163 30650541374322829976149745)
              ·
                refine ⟨22987906030742122482112309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30650541374322829976149745 22987906030742122482112309)
                ·
                  refine ⟨2155116190382073982698029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22987906030742122482112309 2155116190382073982698029)
                  ·
                    refine ⟨808168571393277743511761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155116190382073982698029 808168571393277743511761)
                    ·
                      refine ⟨606126428544958307633821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808168571393277743511761 606126428544958307633821)
                      ·
                        rfl

theorem cell23_1180427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 3, 2].length) (baseStart_1180427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180427 prefixEnd_1180427 := by exact prefixLift 1180427
  have htrace : WordTrace (prefixWord ++ tailWord_1180427) baseStart_1180427 baseEnd_1180427 := by
    simpa [prefixWord, tailWord_1180427, baseEnd_1180427] using wordTrace_append hprefix tailTrace_1180427
  have hstable : (prefixWord ++ tailWord_1180427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180427).length < 2 ^ (prefixWord ++ tailWord_1180427).sum := by decide
  have hdescent : baseEnd_1180427 < baseStart_1180427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180430 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1180430 : Nat := 118140960795 + 1180430 * 2 ^ 59
def prefixEnd_1180430 : Nat := 4983230072969 + 3 ^ 40 * 1180430 * 2
def baseEnd_1180430 : Nat := 606127968986921795896307

theorem tailTrace_1180430 : CollatzResearch.WordTrace tailWord_1180430 prefixEnd_1180430 606127968986921795896307 := by
  unfold tailWord_1180430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381727389188898279850343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28702546075674124159201829 5381727389188898279850343)
  ·
    refine ⟨8072591083783347419775515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5381727389188898279850343 8072591083783347419775515)
    ·
      refine ⟨12108886625675021129663273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8072591083783347419775515 12108886625675021129663273)
      ·
        refine ⟨9081664969256265847247455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12108886625675021129663273 9081664969256265847247455)
        ·
          refine ⟨13622497453884398770871183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081664969256265847247455 13622497453884398770871183)
          ·
            refine ⟨20433746180826598156306775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13622497453884398770871183 20433746180826598156306775)
            ·
              refine ⟨30650619271239897234460163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20433746180826598156306775 30650619271239897234460163)
              ·
                refine ⟨45975928906859845851690245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30650619271239897234460163 45975928906859845851690245)
                ·
                  refine ⟨8620486670036221097191921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45975928906859845851690245 8620486670036221097191921)
                  ·
                    refine ⟨6465365002527165822893941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8620486670036221097191921 6465365002527165822893941)
                    ·
                      refine ⟨606127968986921795896307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6465365002527165822893941 606127968986921795896307)
                      ·
                        rfl

theorem cell23_1180430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1180430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180430 prefixEnd_1180430 := by exact prefixLift 1180430
  have htrace : WordTrace (prefixWord ++ tailWord_1180430) baseStart_1180430 baseEnd_1180430 := by
    simpa [prefixWord, tailWord_1180430, baseEnd_1180430] using wordTrace_append hprefix tailTrace_1180430
  have hstable : (prefixWord ++ tailWord_1180430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180430).length < 2 ^ (prefixWord ++ tailWord_1180430).sum := by decide
  have hdescent : baseEnd_1180430 < baseStart_1180430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180440 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1180440 : Nat := 118140960795 + 1180440 * 2 ^ 59
def prefixEnd_1180440 : Nat := 4983230072969 + 3 ^ 40 * 1180440 * 2
def baseEnd_1180440 : Nat := 606133103793466756771261

theorem tailTrace_1180440 : CollatzResearch.WordTrace tailWord_1180440 prefixEnd_1180440 606133103793466756771261 := by
  unfold tailWord_1180440
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527091921737478973333387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28702789228983305297777849 21527091921737478973333387)
  ·
    refine ⟨32290637882606218460000081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21527091921737478973333387 32290637882606218460000081)
    ·
      refine ⟨24217978411954663845000061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32290637882606218460000081 24217978411954663845000061)
      ·
        refine ⟨9081741904482998941875023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24217978411954663845000061 9081741904482998941875023)
        ·
          refine ⟨13622612856724498412812535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081741904482998941875023 13622612856724498412812535)
          ·
            refine ⟨20433919285086747619218803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13622612856724498412812535 20433919285086747619218803)
            ·
              refine ⟨30650878927630121428828205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20433919285086747619218803 30650878927630121428828205)
              ·
                refine ⟨11494079597861295535810577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30650878927630121428828205 11494079597861295535810577)
                ·
                  refine ⟨8620559698395971651857933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11494079597861295535810577 8620559698395971651857933)
                  ·
                    refine ⟨3232709886898489369446725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8620559698395971651857933 3232709886898489369446725)
                    ·
                      refine ⟨606133103793466756771261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3232709886898489369446725 606133103793466756771261)
                      ·
                        rfl

theorem cell23_1180440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1180440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180440 prefixEnd_1180440 := by exact prefixLift 1180440
  have htrace : WordTrace (prefixWord ++ tailWord_1180440) baseStart_1180440 baseEnd_1180440 := by
    simpa [prefixWord, tailWord_1180440, baseEnd_1180440] using wordTrace_append hprefix tailTrace_1180440
  have hstable : (prefixWord ++ tailWord_1180440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180440).length < 2 ^ (prefixWord ++ tailWord_1180440).sum := by decide
  have hdescent : baseEnd_1180440 < baseStart_1180440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180445 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1180445 : Nat := 118140960795 + 1180445 * 2 ^ 59
def prefixEnd_1180445 : Nat := 4983230072969 + 3 ^ 40 * 1180445 * 2
def baseEnd_1180445 : Nat := 202045223732246412402913

theorem tailTrace_1180445 : CollatzResearch.WordTrace tailWord_1180445 prefixEnd_1180445 202045223732246412402913 := by
  unfold tailWord_1180445
  simp only [CollatzResearch.WordTrace]
  refine ⟨43054366208456843800598789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28702910805637895867065859 43054366208456843800598789)
  ·
    refine ⟨8072693664085658212612273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43054366208456843800598789 8072693664085658212612273)
    ·
      refine ⟨6054520248064243659459205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8072693664085658212612273 6054520248064243659459205)
      ·
        refine ⟨1135222546512045686148601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6054520248064243659459205 1135222546512045686148601)
        ·
          refine ⟨851416909884034264611451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135222546512045686148601 851416909884034264611451)
          ·
            refine ⟨1277125364826051396917177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851416909884034264611451 1277125364826051396917177)
            ·
              refine ⟨957844023619538547687883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277125364826051396917177 957844023619538547687883)
              ·
                refine ⟨1436766035429307821531825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957844023619538547687883 1436766035429307821531825)
                ·
                  refine ⟨1077574526571980866148869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436766035429307821531825 1077574526571980866148869)
                  ·
                    refine ⟨202045223732246412402913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1077574526571980866148869 202045223732246412402913)
                    ·
                      rfl

theorem cell23_1180445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1180445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180445 prefixEnd_1180445 := by exact prefixLift 1180445
  have htrace : WordTrace (prefixWord ++ tailWord_1180445) baseStart_1180445 baseEnd_1180445 := by
    simpa [prefixWord, tailWord_1180445, baseEnd_1180445] using wordTrace_append hprefix tailTrace_1180445
  have hstable : (prefixWord ++ tailWord_1180445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180445).length < 2 ^ (prefixWord ++ tailWord_1180445).sum := by decide
  have hdescent : baseEnd_1180445 < baseStart_1180445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180460 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1180460 : Nat := 118140960795 + 1180460 * 2 ^ 59
def prefixEnd_1180460 : Nat := 4983230072969 + 3 ^ 40 * 1180460 * 2
def baseEnd_1180460 : Nat := 606143373406556678521169

theorem tailTrace_1180460 : CollatzResearch.WordTrace tailWord_1180460 prefixEnd_1180460 606143373406556678521169 := by
  unfold tailWord_1180460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527456651701250681197417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28703275535601667574929889 21527456651701250681197417)
  ·
    refine ⟨16145592488775938010898063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21527456651701250681197417 16145592488775938010898063)
    ·
      refine ⟨24218388733163907016347095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16145592488775938010898063 24218388733163907016347095)
      ·
        refine ⟨36327583099745860524520643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24218388733163907016347095 36327583099745860524520643)
        ·
          refine ⟨54491374649618790786780965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36327583099745860524520643 54491374649618790786780965)
          ·
            refine ⟨10217132746803523272521431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54491374649618790786780965 10217132746803523272521431)
            ·
              refine ⟨15325699120205284908782147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217132746803523272521431 15325699120205284908782147)
              ·
                refine ⟨22988548680307927363173221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15325699120205284908782147 22988548680307927363173221)
                ·
                  refine ⟨4310352877557736380594979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22988548680307927363173221 4310352877557736380594979)
                  ·
                    refine ⟨6465529316336604570892469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4310352877557736380594979 6465529316336604570892469)
                    ·
                      refine ⟨606143373406556678521169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6465529316336604570892469 606143373406556678521169)
                      ·
                        rfl

theorem cell23_1180460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1180460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180460 prefixEnd_1180460 := by exact prefixLift 1180460
  have htrace : WordTrace (prefixWord ++ tailWord_1180460) baseStart_1180460 baseEnd_1180460 := by
    simpa [prefixWord, tailWord_1180460, baseEnd_1180460] using wordTrace_append hprefix tailTrace_1180460
  have hstable : (prefixWord ++ tailWord_1180460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180460).length < 2 ^ (prefixWord ++ tailWord_1180460).sum := by decide
  have hdescent : baseEnd_1180460 < baseStart_1180460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180486 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1180486 : Nat := 118140960795 + 1180486 * 2 ^ 59
def prefixEnd_1180486 : Nat := 4983230072969 + 3 ^ 40 * 1180486 * 2
def baseEnd_1180486 : Nat := 606156723903573576796051

theorem tailTrace_1180486 : CollatzResearch.WordTrace tailWord_1180486 prefixEnd_1180486 606156723903573576796051 := by
  unfold tailWord_1180486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345495675040884618838791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28703907734205538535227541 1345495675040884618838791)
  ·
    refine ⟨2018243512561326928258187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345495675040884618838791 2018243512561326928258187)
    ·
      refine ⟨3027365268841990392387281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018243512561326928258187 3027365268841990392387281)
      ·
        refine ⟨2270523951631492794290461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027365268841990392387281 2270523951631492794290461)
        ·
          refine ⟨851446481861809797858923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2270523951631492794290461 851446481861809797858923)
          ·
            refine ⟨1277169722792714696788385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851446481861809797858923 1277169722792714696788385)
            ·
              refine ⟨957877292094536022591289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277169722792714696788385 957877292094536022591289)
              ·
                refine ⟨718407969070902016943467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957877292094536022591289 718407969070902016943467)
                ·
                  refine ⟨1077611953606353025415201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718407969070902016943467 1077611953606353025415201)
                  ·
                    refine ⟨808208965204764769061401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077611953606353025415201 808208965204764769061401)
                    ·
                      refine ⟨606156723903573576796051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808208965204764769061401 606156723903573576796051)
                      ·
                        rfl

theorem cell23_1180486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1180486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180486 prefixEnd_1180486 := by exact prefixLift 1180486
  have htrace : WordTrace (prefixWord ++ tailWord_1180486) baseStart_1180486 baseEnd_1180486 := by
    simpa [prefixWord, tailWord_1180486, baseEnd_1180486] using wordTrace_append hprefix tailTrace_1180486
  have hstable : (prefixWord ++ tailWord_1180486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180486).length < 2 ^ (prefixWord ++ tailWord_1180486).sum := by decide
  have hdescent : baseEnd_1180486 < baseStart_1180486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180508 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1180508 : Nat := 118140960795 + 1180508 * 2 ^ 59
def prefixEnd_1180508 : Nat := 4983230072969 + 3 ^ 40 * 1180508 * 2
def baseEnd_1180508 : Nat := 606168020477972490720949

theorem tailTrace_1180508 : CollatzResearch.WordTrace tailWord_1180508 prefixEnd_1180508 606168020477972490720949 := by
  unfold tailWord_1180508
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528332003614302780071089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28704442671485737040094785 21528332003614302780071089)
  ·
    refine ⟨16146249002710727085053317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21528332003614302780071089 16146249002710727085053317)
    ·
      refine ⟨3027421688008261328447497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16146249002710727085053317 3027421688008261328447497)
      ·
        refine ⟨2270566266006195996335623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027421688008261328447497 2270566266006195996335623)
        ·
          refine ⟨3405849399009293994503435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270566266006195996335623 3405849399009293994503435)
          ·
            refine ⟨5108774098513940991755153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405849399009293994503435 5108774098513940991755153)
            ·
              refine ⟨3831580573885455743816365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108774098513940991755153 3831580573885455743816365)
              ·
                refine ⟨1436842715207045903931137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831580573885455743816365 1436842715207045903931137)
                ·
                  refine ⟨1077632036405284427948353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436842715207045903931137 1077632036405284427948353)
                  ·
                    refine ⟨808224027303963320961265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077632036405284427948353 808224027303963320961265)
                    ·
                      refine ⟨606168020477972490720949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808224027303963320961265 606168020477972490720949)
                      ·
                        rfl

theorem cell23_1180508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1180508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180508 prefixEnd_1180508 := by exact prefixLift 1180508
  have htrace : WordTrace (prefixWord ++ tailWord_1180508) baseStart_1180508 baseEnd_1180508 := by
    simpa [prefixWord, tailWord_1180508, baseEnd_1180508] using wordTrace_append hprefix tailTrace_1180508
  have hstable : (prefixWord ++ tailWord_1180508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180508).length < 2 ^ (prefixWord ++ tailWord_1180508).sum := by decide
  have hdescent : baseEnd_1180508 < baseStart_1180508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180514 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1180514 : Nat := 118140960795 + 1180514 * 2 ^ 59
def prefixEnd_1180514 : Nat := 4983230072969 + 3 ^ 40 * 1180514 * 2
def baseEnd_1180514 : Nat := 67352344595766607471769

theorem tailTrace_1180514 : CollatzResearch.WordTrace tailWord_1180514 prefixEnd_1180514 67352344595766607471769 := by
  unfold tailWord_1180514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764220711301717146215149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28704588563471245723240397 10764220711301717146215149)
  ·
    refine ⟨4036582766738143929830681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10764220711301717146215149 4036582766738143929830681)
    ·
      refine ⟨3027437075053607947373011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4036582766738143929830681 3027437075053607947373011)
      ·
        refine ⟨4541155612580411921059517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027437075053607947373011 4541155612580411921059517)
        ·
          refine ⟨1702933354717654470397319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4541155612580411921059517 1702933354717654470397319)
          ·
            refine ⟨2554400032076481705595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702933354717654470397319 2554400032076481705595979)
            ·
              refine ⟨3831600048114722558393969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554400032076481705595979 3831600048114722558393969)
              ·
                refine ⟨2873700036086041918795477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831600048114722558393969 2873700036086041918795477)
                ·
                  refine ⟨67352344595766607471769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2873700036086041918795477 67352344595766607471769)
                  ·
                    rfl

theorem cell23_1180514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1180514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180514 prefixEnd_1180514 := by exact prefixLift 1180514
  have htrace : WordTrace (prefixWord ++ tailWord_1180514) baseStart_1180514 baseEnd_1180514 := by
    simpa [prefixWord, tailWord_1180514, baseEnd_1180514] using wordTrace_append hprefix tailTrace_1180514
  have hstable : (prefixWord ++ tailWord_1180514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180514).length < 2 ^ (prefixWord ++ tailWord_1180514).sum := by decide
  have hdescent : baseEnd_1180514 < baseStart_1180514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180540 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1180540 : Nat := 118140960795 + 1180540 * 2 ^ 59
def prefixEnd_1180540 : Nat := 4983230072969 + 3 ^ 40 * 1180540 * 2
def baseEnd_1180540 : Nat := 202061483952972121840267

theorem tailTrace_1180540 : CollatzResearch.WordTrace tailWord_1180540 prefixEnd_1180540 202061483952972121840267 := by
  unfold tailWord_1180540
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528915571556337512653537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28705220762075116683538049 21528915571556337512653537)
  ·
    refine ⟨16146686678667253134490153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21528915571556337512653537 16146686678667253134490153)
    ·
      refine ⟨12110015009000439850867615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16146686678667253134490153 12110015009000439850867615)
      ·
        refine ⟨18165022513500659776301423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12110015009000439850867615 18165022513500659776301423)
        ·
          refine ⟨27247533770250989664452135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18165022513500659776301423 27247533770250989664452135)
          ·
            refine ⟨40871300655376484496678203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27247533770250989664452135 40871300655376484496678203)
            ·
              refine ⟨61306950983064726745017305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40871300655376484496678203 61306950983064726745017305)
              ·
                refine ⟨45980213237298545058762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61306950983064726745017305 45980213237298545058762979)
                ·
                  refine ⟨68970319855947817588144469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45980213237298545058762979 68970319855947817588144469)
                  ·
                    refine ⟨202061483952972121840267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 68970319855947817588144469 202061483952972121840267)
                    ·
                      rfl

theorem cell23_1180540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1180540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180540 prefixEnd_1180540 := by exact prefixLift 1180540
  have htrace : WordTrace (prefixWord ++ tailWord_1180540) baseStart_1180540 baseEnd_1180540 := by
    simpa [prefixWord, tailWord_1180540, baseEnd_1180540] using wordTrace_append hprefix tailTrace_1180540
  have hstable : (prefixWord ++ tailWord_1180540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180540).length < 2 ^ (prefixWord ++ tailWord_1180540).sum := by decide
  have hdescent : baseEnd_1180540 < baseStart_1180540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180542 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1180542 : Nat := 118140960795 + 1180542 * 2 ^ 59
def prefixEnd_1180542 : Nat := 4983230072969 + 3 ^ 40 * 1180542 * 2
def baseEnd_1180542 : Nat := 606185478820225357695793

theorem tailTrace_1180542 : CollatzResearch.WordTrace tailWord_1180542 prefixEnd_1180542 606185478820225357695793 := by
  unfold tailWord_1180542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382238011138178670859985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28705269392736952911253253 5382238011138178670859985)
  ·
    refine ⟨4036678508353634003144989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5382238011138178670859985 4036678508353634003144989)
    ·
      refine ⟨1513754440632612751179371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4036678508353634003144989 1513754440632612751179371)
      ·
        refine ⟨2270631660948919126769057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513754440632612751179371 2270631660948919126769057)
        ·
          refine ⟨1702973745711689345076793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270631660948919126769057 1702973745711689345076793)
          ·
            refine ⟨1277230309283767008807595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702973745711689345076793 1277230309283767008807595)
            ·
              refine ⟨1915845463925650513211393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277230309283767008807595 1915845463925650513211393)
              ·
                refine ⟨1436884097944237884908545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915845463925650513211393 1436884097944237884908545)
                ·
                  refine ⟨1077663073458178413681409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1436884097944237884908545 1077663073458178413681409)
                  ·
                    refine ⟨808247305093633810261057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077663073458178413681409 808247305093633810261057)
                    ·
                      refine ⟨606185478820225357695793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808247305093633810261057 606185478820225357695793)
                      ·
                        rfl

theorem cell23_1180542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1180542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180542 prefixEnd_1180542 := by exact prefixLift 1180542
  have htrace : WordTrace (prefixWord ++ tailWord_1180542) baseStart_1180542 baseEnd_1180542 := by
    simpa [prefixWord, tailWord_1180542, baseEnd_1180542] using wordTrace_append hprefix tailTrace_1180542
  have hstable : (prefixWord ++ tailWord_1180542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180542).length < 2 ^ (prefixWord ++ tailWord_1180542).sum := by decide
  have hdescent : baseEnd_1180542 < baseStart_1180542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180547 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4]
def baseStart_1180547 : Nat := 118140960795 + 1180547 * 2 ^ 59
def prefixEnd_1180547 : Nat := 4983230072969 + 3 ^ 40 * 1180547 * 2
def baseEnd_1180547 : Nat := 606188046223497838133269

theorem tailTrace_1180547 : CollatzResearch.WordTrace tailWord_1180547 prefixEnd_1180547 606188046223497838133269 := by
  unfold tailWord_1180547
  simp only [CollatzResearch.WordTrace]
  refine ⟨43058086454087315220811895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28705390969391543480541263 43058086454087315220811895)
  ·
    refine ⟨64587129681130972831217843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43058086454087315220811895 64587129681130972831217843)
    ·
      refine ⟨96880694521696459246826765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64587129681130972831217843 96880694521696459246826765)
      ·
        refine ⟨36330260445636172217560037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96880694521696459246826765 36330260445636172217560037)
        ·
          refine ⟨6811923833556782290792507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36330260445636172217560037 6811923833556782290792507)
          ·
            refine ⟨10217885750335173436188761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811923833556782290792507 10217885750335173436188761)
            ·
              refine ⟨7663414312751380077141571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10217885750335173436188761 7663414312751380077141571)
              ·
                refine ⟨11495121469127070115712357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663414312751380077141571 11495121469127070115712357)
                ·
                  refine ⟨2155335275461325646696067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11495121469127070115712357 2155335275461325646696067)
                  ·
                    refine ⟨3233002913191988470044101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155335275461325646696067 3233002913191988470044101)
                    ·
                      refine ⟨606188046223497838133269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3233002913191988470044101 606188046223497838133269)
                      ·
                        rfl

theorem cell23_1180547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_1180547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180547 prefixEnd_1180547 := by exact prefixLift 1180547
  have htrace : WordTrace (prefixWord ++ tailWord_1180547) baseStart_1180547 baseEnd_1180547 := by
    simpa [prefixWord, tailWord_1180547, baseEnd_1180547] using wordTrace_append hprefix tailTrace_1180547
  have hstable : (prefixWord ++ tailWord_1180547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180547).length < 2 ^ (prefixWord ++ tailWord_1180547).sum := by decide
  have hdescent : baseEnd_1180547 < baseStart_1180547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1180560 : Nat := 118140960795 + 1180560 * 2 ^ 59
def prefixEnd_1180560 : Nat := 4983230072969 + 3 ^ 40 * 1180560 * 2
def baseEnd_1180560 : Nat := 606194721472006287270709

theorem tailTrace_1180560 : CollatzResearch.WordTrace tailWord_1180560 prefixEnd_1180560 606194721472006287270709 := by
  unfold tailWord_1180560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529280301520109220517567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28705707068693478960690089 21529280301520109220517567)
  ·
    refine ⟨32293920452280163830776351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21529280301520109220517567 32293920452280163830776351)
    ·
      refine ⟨48440880678420245746164527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32293920452280163830776351 48440880678420245746164527)
      ·
        refine ⟨72661321017630368619246791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48440880678420245746164527 72661321017630368619246791)
        ·
          refine ⟨108991981526445552928870187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72661321017630368619246791 108991981526445552928870187)
          ·
            refine ⟨163487972289668329393305281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108991981526445552928870187 163487972289668329393305281)
            ·
              refine ⟨122615979217251247044978961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163487972289668329393305281 122615979217251247044978961)
              ·
                refine ⟨91961984412938435283734221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122615979217251247044978961 91961984412938435283734221)
                ·
                  refine ⟨34485744154851913231400333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91961984412938435283734221 34485744154851913231400333)
                  ·
                    refine ⟨12932154058069467461775125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34485744154851913231400333 12932154058069467461775125)
                    ·
                      refine ⟨606194721472006287270709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12932154058069467461775125 606194721472006287270709)
                      ·
                        rfl

theorem cell23_1180560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1180560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180560 prefixEnd_1180560 := by exact prefixLift 1180560
  have htrace : WordTrace (prefixWord ++ tailWord_1180560) baseStart_1180560 baseEnd_1180560 := by
    simpa [prefixWord, tailWord_1180560, baseEnd_1180560] using wordTrace_append hprefix tailTrace_1180560
  have hstable : (prefixWord ++ tailWord_1180560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180560).length < 2 ^ (prefixWord ++ tailWord_1180560).sum := by decide
  have hdescent : baseEnd_1180560 < baseStart_1180560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180567 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1180567 : Nat := 118140960795 + 1180567 * 2 ^ 59
def prefixEnd_1180567 : Nat := 4983230072969 + 3 ^ 40 * 1180567 * 2
def baseEnd_1180567 : Nat := 606198315836587759883177

theorem tailTrace_1180567 : CollatzResearch.WordTrace tailWord_1180567 prefixEnd_1180567 606198315836587759883177 := by
  unfold tailWord_1180567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43058815914014858636539955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28705877276009905757693303 43058815914014858636539955)
  ·
    refine ⟨64588223871022287954809933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43058815914014858636539955 64588223871022287954809933)
    ·
      refine ⟨24220583951633357983053725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64588223871022287954809933 24220583951633357983053725)
      ·
        refine ⟨9082718981862509243645147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24220583951633357983053725 9082718981862509243645147)
        ·
          refine ⟨13624078472793763865467721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9082718981862509243645147 13624078472793763865467721)
          ·
            refine ⟨10218058854595322899100791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13624078472793763865467721 10218058854595322899100791)
            ·
              refine ⟨15327088281892984348651187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10218058854595322899100791 15327088281892984348651187)
              ·
                refine ⟨22990632422839476522976781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15327088281892984348651187 22990632422839476522976781)
                ·
                  refine ⟨8621487158564803696116293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22990632422839476522976781 8621487158564803696116293)
                  ·
                    refine ⟨1616528842230900693021805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8621487158564803696116293 1616528842230900693021805)
                    ·
                      refine ⟨606198315836587759883177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1616528842230900693021805 606198315836587759883177)
                      ·
                        rfl

theorem cell23_1180567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1180567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180567 prefixEnd_1180567 := by exact prefixLift 1180567
  have htrace : WordTrace (prefixWord ++ tailWord_1180567) baseStart_1180567 baseEnd_1180567 := by
    simpa [prefixWord, tailWord_1180567, baseEnd_1180567] using wordTrace_append hprefix tailTrace_1180567
  have hstable : (prefixWord ++ tailWord_1180567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180567).length < 2 ^ (prefixWord ++ tailWord_1180567).sum := by decide
  have hdescent : baseEnd_1180567 < baseStart_1180567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180608 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 1, 4]
def baseStart_1180608 : Nat := 118140960795 + 1180608 * 2 ^ 59
def prefixEnd_1180608 : Nat := 4983230072969 + 3 ^ 40 * 1180608 * 2
def baseEnd_1180608 : Nat := 202073122847807366490163

theorem tailTrace_1180608 : CollatzResearch.WordTrace tailWord_1180608 prefixEnd_1180608 202073122847807366490163 := by
  unfold tailWord_1180608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21530155653433161319391239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28706874204577548425854985 21530155653433161319391239)
  ·
    refine ⟨32295233480149741979086859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21530155653433161319391239 32295233480149741979086859)
    ·
      refine ⟨48442850220224612968630289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32295233480149741979086859 48442850220224612968630289)
      ·
        refine ⟨36332137665168459726472717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48442850220224612968630289 36332137665168459726472717)
        ·
          refine ⟨13624551624438172397427269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36332137665168459726472717 13624551624438172397427269)
          ·
            refine ⟨2554603429582157324517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13624551624438172397427269 2554603429582157324517613)
            ·
              refine ⟨957976286093308996694105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2554603429582157324517613 957976286093308996694105)
              ·
                refine ⟨718482214569981747520579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957976286093308996694105 718482214569981747520579)
                ·
                  refine ⟨1077723321854972621280869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718482214569981747520579 1077723321854972621280869)
                  ·
                    refine ⟨202073122847807366490163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1077723321854972621280869 202073122847807366490163)
                    ·
                      rfl

theorem cell23_1180608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 4].length) (baseStart_1180608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180608 prefixEnd_1180608 := by exact prefixLift 1180608
  have htrace : WordTrace (prefixWord ++ tailWord_1180608) baseStart_1180608 baseEnd_1180608 := by
    simpa [prefixWord, tailWord_1180608, baseEnd_1180608] using wordTrace_append hprefix tailTrace_1180608
  have hstable : (prefixWord ++ tailWord_1180608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180608).length < 2 ^ (prefixWord ++ tailWord_1180608).sum := by decide
  have hdescent : baseEnd_1180608 < baseStart_1180608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180624 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2]
def baseStart_1180624 : Nat := 118140960795 + 1180624 * 2 ^ 59
def prefixEnd_1180624 : Nat := 4983230072969 + 3 ^ 40 * 1180624 * 2
def baseEnd_1180624 : Nat := 606227584233894036870415

theorem tailTrace_1180624 : CollatzResearch.WordTrace tailWord_1180624 prefixEnd_1180624 606227584233894036870415 := by
  unfold tailWord_1180624
  simp only [CollatzResearch.WordTrace]
  refine ⟨21530447437404178685682463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28707263249872238247576617 21530447437404178685682463)
  ·
    refine ⟨32295671156106268028523695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21530447437404178685682463 32295671156106268028523695)
    ·
      refine ⟨48443506734159402042785543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32295671156106268028523695 48443506734159402042785543)
      ·
        refine ⟨72665260101239103064178315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48443506734159402042785543 72665260101239103064178315)
        ·
          refine ⟨108997890151858654596267473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72665260101239103064178315 108997890151858654596267473)
          ·
            refine ⟨81748417613893990947200605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108997890151858654596267473 81748417613893990947200605)
            ·
              refine ⟨30655656605210246605200227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81748417613893990947200605 30655656605210246605200227)
              ·
                refine ⟨45983484907815369907800341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30655656605210246605200227 45983484907815369907800341)
                ·
                  refine ⟨2155475855053845464428141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45983484907815369907800341 2155475855053845464428141)
                  ·
                    refine ⟨808303445645192049160553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155475855053845464428141 808303445645192049160553)
                    ·
                      refine ⟨606227584233894036870415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808303445645192049160553 606227584233894036870415)
                      ·
                        rfl

theorem cell23_1180624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2].length) (baseStart_1180624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180624 prefixEnd_1180624 := by exact prefixLift 1180624
  have htrace : WordTrace (prefixWord ++ tailWord_1180624) baseStart_1180624 baseEnd_1180624 := by
    simpa [prefixWord, tailWord_1180624, baseEnd_1180624] using wordTrace_append hprefix tailTrace_1180624
  have hstable : (prefixWord ++ tailWord_1180624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180624).length < 2 ^ (prefixWord ++ tailWord_1180624).sum := by decide
  have hdescent : baseEnd_1180624 < baseStart_1180624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180634 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_1180634 : Nat := 118140960795 + 1180634 * 2 ^ 59
def prefixEnd_1180634 : Nat := 4983230072969 + 3 ^ 40 * 1180634 * 2
def baseEnd_1180634 : Nat := 202077573013479665915123

theorem tailTrace_1180634 : CollatzResearch.WordTrace tailWord_1180634 prefixEnd_1180634 202077573013479665915123 := by
  unfold tailWord_1180634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10765314901193032269807239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28707506403181419386152637 10765314901193032269807239)
  ·
    refine ⟨16147972351789548404710859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10765314901193032269807239 16147972351789548404710859)
    ·
      refine ⟨24221958527684322607066289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16147972351789548404710859 24221958527684322607066289)
      ·
        refine ⟨18166468895763241955299717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24221958527684322607066289 18166468895763241955299717)
        ·
          refine ⟨3406212917955607866618697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18166468895763241955299717 3406212917955607866618697)
          ·
            refine ⟨2554659688466705899964023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406212917955607866618697 2554659688466705899964023)
            ·
              refine ⟨3831989532700058849946035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554659688466705899964023 3831989532700058849946035)
              ·
                refine ⟨5747984299050088274919053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831989532700058849946035 5747984299050088274919053)
                ·
                  refine ⟨2155494112143783103094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5747984299050088274919053 2155494112143783103094645)
                  ·
                    refine ⟨202077573013479665915123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2155494112143783103094645 202077573013479665915123)
                    ·
                      rfl

theorem cell23_1180634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_1180634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180634 prefixEnd_1180634 := by exact prefixLift 1180634
  have htrace : WordTrace (prefixWord ++ tailWord_1180634) baseStart_1180634 baseEnd_1180634 := by
    simpa [prefixWord, tailWord_1180634, baseEnd_1180634] using wordTrace_append hprefix tailTrace_1180634
  have hstable : (prefixWord ++ tailWord_1180634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180634).length < 2 ^ (prefixWord ++ tailWord_1180634).sum := by decide
  have hdescent : baseEnd_1180634 < baseStart_1180634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180667 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_1180667 : Nat := 118140960795 + 1180667 * 2 ^ 59
def prefixEnd_1180667 : Nat := 4983230072969 + 3 ^ 40 * 1180667 * 2
def baseEnd_1180667 : Nat := 606249663902037368632717

theorem tailTrace_1180667 : CollatzResearch.WordTrace tailWord_1180667 prefixEnd_1180667 606249663902037368632717 := by
  unfold tailWord_1180667
  simp only [CollatzResearch.WordTrace]
  refine ⟨43062463213652575715180255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28708308809101717143453503 43062463213652575715180255)
  ·
    refine ⟨64593694820478863572770383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43062463213652575715180255 64593694820478863572770383)
    ·
      refine ⟨96890542230718295359155575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64593694820478863572770383 96890542230718295359155575)
      ·
        refine ⟨145335813346077443038733363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96890542230718295359155575 145335813346077443038733363)
        ·
          refine ⟨218003720019116164558100045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145335813346077443038733363 218003720019116164558100045)
          ·
            refine ⟨81751395007168561709287517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218003720019116164558100045 81751395007168561709287517)
            ·
              refine ⟨30656773127688210640982819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81751395007168561709287517 30656773127688210640982819)
              ·
                refine ⟨45985159691532315961474229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30656773127688210640982819 45985159691532315961474229)
                ·
                  refine ⟨4311108721081154621388209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45985159691532315961474229 4311108721081154621388209)
                  ·
                    refine ⟨3233331540810865966041157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311108721081154621388209 3233331540810865966041157)
                    ·
                      refine ⟨606249663902037368632717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3233331540810865966041157 606249663902037368632717)
                      ·
                        rfl

theorem cell23_1180667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_1180667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180667 prefixEnd_1180667 := by exact prefixLift 1180667
  have htrace : WordTrace (prefixWord ++ tailWord_1180667) baseStart_1180667 baseEnd_1180667 := by
    simpa [prefixWord, tailWord_1180667, baseEnd_1180667] using wordTrace_append hprefix tailTrace_1180667
  have hstable : (prefixWord ++ tailWord_1180667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180667).length < 2 ^ (prefixWord ++ tailWord_1180667).sum := by decide
  have hdescent : baseEnd_1180667 < baseStart_1180667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180684 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1180684 : Nat := 118140960795 + 1180684 * 2 ^ 59
def prefixEnd_1180684 : Nat := 4983230072969 + 3 ^ 40 * 1180684 * 2
def baseEnd_1180684 : Nat := 606258393073163802120139

theorem tailTrace_1180684 : CollatzResearch.WordTrace tailWord_1180684 prefixEnd_1180684 606258393073163802120139 := by
  unfold tailWord_1180684
  simp only [CollatzResearch.WordTrace]
  refine ⟨21531541627295493809274553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28708722169727325079032737 21531541627295493809274553)
  ·
    refine ⟨16148656220471620356955915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21531541627295493809274553 16148656220471620356955915)
    ·
      refine ⟨24222984330707430535433873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16148656220471620356955915 24222984330707430535433873)
      ·
        refine ⟨18167238248030572901575405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24222984330707430535433873 18167238248030572901575405)
        ·
          refine ⟨6812714343011464838090777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18167238248030572901575405 6812714343011464838090777)
          ·
            refine ⟨5109535757258598628568083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6812714343011464838090777 5109535757258598628568083)
            ·
              refine ⟨7664303635887897942852125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109535757258598628568083 7664303635887897942852125)
              ·
                refine ⟨2874113863457961728569547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7664303635887897942852125 2874113863457961728569547)
                ·
                  refine ⟨4311170795186942592854321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874113863457961728569547 4311170795186942592854321)
                  ·
                    refine ⟨3233378096390206944640741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311170795186942592854321 3233378096390206944640741)
                    ·
                      refine ⟨606258393073163802120139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3233378096390206944640741 606258393073163802120139)
                      ·
                        rfl

theorem cell23_1180684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1180684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180684 prefixEnd_1180684 := by exact prefixLift 1180684
  have htrace : WordTrace (prefixWord ++ tailWord_1180684) baseStart_1180684 baseEnd_1180684 := by
    simpa [prefixWord, tailWord_1180684, baseEnd_1180684] using wordTrace_append hprefix tailTrace_1180684
  have hstable : (prefixWord ++ tailWord_1180684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180684).length < 2 ^ (prefixWord ++ tailWord_1180684).sum := by decide
  have hdescent : baseEnd_1180684 < baseStart_1180684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180705 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1180705 : Nat := 118140960795 + 1180705 * 2 ^ 59
def prefixEnd_1180705 : Nat := 4983230072969 + 3 ^ 40 * 1180705 * 2
def baseEnd_1180705 : Nat := 606269176166908219957543

theorem tailTrace_1180705 : CollatzResearch.WordTrace tailWord_1180705 prefixEnd_1180705 606269176166908219957543 := by
  unfold tailWord_1180705
  simp only [CollatzResearch.WordTrace]
  refine ⟨43063849187514908205063569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28709232791676605470042379 43063849187514908205063569)
  ·
    refine ⟨32297886890636181153797677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43063849187514908205063569 32297886890636181153797677)
    ·
      refine ⟨12111707583988567932674129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32297886890636181153797677 12111707583988567932674129)
      ·
        refine ⟨9083780687991425949505597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12111707583988567932674129 9083780687991425949505597)
        ·
          refine ⟨3406417757996784731064599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9083780687991425949505597 3406417757996784731064599)
          ·
            refine ⟨5109626636995177096596899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406417757996784731064599 5109626636995177096596899)
            ·
              refine ⟨7664439955492765644895349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109626636995177096596899 7664439955492765644895349)
              ·
                refine ⟨718541245827446779208939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7664439955492765644895349 718541245827446779208939)
                ·
                  refine ⟨1077811868741170168813409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718541245827446779208939 1077811868741170168813409)
                  ·
                    refine ⟨808358901555877626610057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1077811868741170168813409 808358901555877626610057)
                    ·
                      refine ⟨606269176166908219957543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808358901555877626610057 606269176166908219957543)
                      ·
                        rfl

theorem cell23_1180705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1180705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180705 prefixEnd_1180705 := by exact prefixLift 1180705
  have htrace : WordTrace (prefixWord ++ tailWord_1180705) baseStart_1180705 baseEnd_1180705 := by
    simpa [prefixWord, tailWord_1180705, baseEnd_1180705] using wordTrace_append hprefix tailTrace_1180705
  have hstable : (prefixWord ++ tailWord_1180705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180705).length < 2 ^ (prefixWord ++ tailWord_1180705).sum := by decide
  have hdescent : baseEnd_1180705 < baseStart_1180705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180708 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1180708 : Nat := 118140960795 + 1180708 * 2 ^ 59
def prefixEnd_1180708 : Nat := 4983230072969 + 3 ^ 40 * 1180708 * 2
def baseEnd_1180708 : Nat := 606270716608871708220029

theorem tailTrace_1180708 : CollatzResearch.WordTrace tailWord_1180708 prefixEnd_1180708 606270716608871708220029 := by
  unfold tailWord_1180708
  simp only [CollatzResearch.WordTrace]
  refine ⟨21531979303252019858711389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28709305737669359811615185 21531979303252019858711389)
  ·
    refine ⟨8074492238719507447016771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21531979303252019858711389 8074492238719507447016771)
    ·
      refine ⟨12111738358079261170525157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8074492238719507447016771 12111738358079261170525157)
      ·
        refine ⟨2270950942139861469473467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12111738358079261170525157 2270950942139861469473467)
        ·
          refine ⟨3406426413209792204210201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270950942139861469473467 3406426413209792204210201)
          ·
            refine ⟨2554819809907344153157651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406426413209792204210201 2554819809907344153157651)
            ·
              refine ⟨3832229714861016229736477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554819809907344153157651 3832229714861016229736477)
              ·
                refine ⟨1437086143072881086151179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832229714861016229736477 1437086143072881086151179)
                ·
                  refine ⟨2155629214609321629226769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437086143072881086151179 2155629214609321629226769)
                  ·
                    refine ⟨1616721910956991221920077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155629214609321629226769 1616721910956991221920077)
                    ·
                      refine ⟨606270716608871708220029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1616721910956991221920077 606270716608871708220029)
                      ·
                        rfl

theorem cell23_1180708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1180708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180708 prefixEnd_1180708 := by exact prefixLift 1180708
  have htrace : WordTrace (prefixWord ++ tailWord_1180708) baseStart_1180708 baseEnd_1180708 := by
    simpa [prefixWord, tailWord_1180708, baseEnd_1180708] using wordTrace_append hprefix tailTrace_1180708
  have hstable : (prefixWord ++ tailWord_1180708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180708).length < 2 ^ (prefixWord ++ tailWord_1180708).sum := by decide
  have hdescent : baseEnd_1180708 < baseStart_1180708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180721 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1180721 : Nat := 118140960795 + 1180721 * 2 ^ 59
def prefixEnd_1180721 : Nat := 4983230072969 + 3 ^ 40 * 1180721 * 2
def baseEnd_1180721 : Nat := 606277391857380157357469

theorem tailTrace_1180721 : CollatzResearch.WordTrace tailWord_1180721 prefixEnd_1180721 606277391857380157357469 := by
  unfold tailWord_1180721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064432755456942937646017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28709621836971295291764011 43064432755456942937646017)
  ·
    refine ⟨32298324566592707203234513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43064432755456942937646017 32298324566592707203234513)
    ·
      refine ⟨24223743424944530402425885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32298324566592707203234513 24223743424944530402425885)
      ·
        refine ⟨9083903784354198900909707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24223743424944530402425885 9083903784354198900909707)
        ·
          refine ⟨13625855676531298351364561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083903784354198900909707 13625855676531298351364561)
          ·
            refine ⟨10219391757398473763523421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13625855676531298351364561 10219391757398473763523421)
            ·
              refine ⟨3832271909024427661321283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10219391757398473763523421 3832271909024427661321283)
              ·
                refine ⟨5748407863536641491981925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832271909024427661321283 5748407863536641491981925)
                ·
                  refine ⟨1077826474413120279746611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5748407863536641491981925 1077826474413120279746611)
                  ·
                    refine ⟨1616739711619680419619917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077826474413120279746611 1616739711619680419619917)
                    ·
                      refine ⟨606277391857380157357469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1616739711619680419619917 606277391857380157357469)
                      ·
                        rfl

theorem cell23_1180721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1180721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180721 prefixEnd_1180721 := by exact prefixLift 1180721
  have htrace : WordTrace (prefixWord ++ tailWord_1180721) baseStart_1180721 baseEnd_1180721 := by
    simpa [prefixWord, tailWord_1180721, baseEnd_1180721] using wordTrace_append hprefix tailTrace_1180721
  have hstable : (prefixWord ++ tailWord_1180721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180721).length < 2 ^ (prefixWord ++ tailWord_1180721).sum := by decide
  have hdescent : baseEnd_1180721 < baseStart_1180721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180789 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1180789 : Nat := 118140960795 + 1180789 * 2 ^ 59
def prefixEnd_1180789 : Nat := 4983230072969 + 3 ^ 40 * 1180789 * 2
def baseEnd_1180789 : Nat := 606312308541885891307157

theorem tailTrace_1180789 : CollatzResearch.WordTrace tailWord_1180789 prefixEnd_1180789 606312308541885891307157 := by
  unfold tailWord_1180789
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066912919210590551121421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28711275279473727034080947 43066912919210590551121421)
  ·
    refine ⟨16150092344703971456670533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43066912919210590551121421 16150092344703971456670533)
    ·
      refine ⟨3028142314631994648125725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16150092344703971456670533 3028142314631994648125725)
      ·
        refine ⟨1135553367986997993047147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3028142314631994648125725 1135553367986997993047147)
        ·
          refine ⟨1703330051980496989570721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135553367986997993047147 1703330051980496989570721)
          ·
            refine ⟨1277497538985372742178041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703330051980496989570721 1277497538985372742178041)
            ·
              refine ⟨958123154239029556633531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277497538985372742178041 958123154239029556633531)
              ·
                refine ⟨1437184731358544334950297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958123154239029556633531 1437184731358544334950297)
                ·
                  refine ⟨1077888548518908251212723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1437184731358544334950297 1077888548518908251212723)
                  ·
                    refine ⟨1616832822778362376819085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1077888548518908251212723 1616832822778362376819085)
                    ·
                      refine ⟨606312308541885891307157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1616832822778362376819085 606312308541885891307157)
                      ·
                        rfl

theorem cell23_1180789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1180789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180789 prefixEnd_1180789 := by exact prefixLift 1180789
  have htrace : WordTrace (prefixWord ++ tailWord_1180789) baseStart_1180789 baseEnd_1180789 := by
    simpa [prefixWord, tailWord_1180789, baseEnd_1180789] using wordTrace_append hprefix tailTrace_1180789
  have hstable : (prefixWord ++ tailWord_1180789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180789).length < 2 ^ (prefixWord ++ tailWord_1180789).sum := by decide
  have hdescent : baseEnd_1180789 < baseStart_1180789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180851 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 6, 2]
def baseStart_1180851 : Nat := 118140960795 + 1180851 * 2 ^ 59
def prefixEnd_1180851 : Nat := 4983230072969 + 3 ^ 40 * 1180851 * 2
def baseEnd_1180851 : Nat := 606344144342464648731871

theorem tailTrace_1180851 : CollatzResearch.WordTrace tailWord_1180851 prefixEnd_1180851 606344144342464648731871 := by
  unfold tailWord_1180851
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069174244985975139878407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28712782829990650093252271 43069174244985975139878407)
  ·
    refine ⟨64603761367478962709817611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43069174244985975139878407 64603761367478962709817611)
    ·
      refine ⟨96905642051218444064726417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64603761367478962709817611 96905642051218444064726417)
      ·
        refine ⟨72679231538413833048544813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96905642051218444064726417 72679231538413833048544813)
        ·
          refine ⟨27254711826905187393204305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72679231538413833048544813 27254711826905187393204305)
          ·
            refine ⟨20441033870178890544903229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27254711826905187393204305 20441033870178890544903229)
            ·
              refine ⟨7665387701317083954338711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20441033870178890544903229 7665387701317083954338711)
              ·
                refine ⟨11498081551975625931508067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665387701317083954338711 11498081551975625931508067)
                ·
                  refine ⟨17247122327963438897262101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11498081551975625931508067 17247122327963438897262101)
                  ·
                    refine ⟨808458859123286198309161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17247122327963438897262101 808458859123286198309161)
                    ·
                      refine ⟨606344144342464648731871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808458859123286198309161 606344144342464648731871)
                      ·
                        rfl

theorem cell23_1180851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6, 2].length) (baseStart_1180851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180851 prefixEnd_1180851 := by exact prefixLift 1180851
  have htrace : WordTrace (prefixWord ++ tailWord_1180851) baseStart_1180851 baseEnd_1180851 := by
    simpa [prefixWord, tailWord_1180851, baseEnd_1180851] using wordTrace_append hprefix tailTrace_1180851
  have hstable : (prefixWord ++ tailWord_1180851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180851).length < 2 ^ (prefixWord ++ tailWord_1180851).sum := by decide
  have hdescent : baseEnd_1180851 < baseStart_1180851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180861 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1180861 : Nat := 118140960795 + 1180861 * 2 ^ 59
def prefixEnd_1180861 : Nat := 4983230072969 + 3 ^ 40 * 1180861 * 2
def baseEnd_1180861 : Nat := 202116426383003203202275

theorem tailTrace_1180861 : CollatzResearch.WordTrace tailWord_1180861 prefixEnd_1180861 202116426383003203202275 := by
  unfold tailWord_1180861
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069538974949746847742437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28713025983299831231828291 43069538974949746847742437)
  ·
    refine ⟨8075538557803077533951707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43069538974949746847742437 8075538557803077533951707)
    ·
      refine ⟨12113307836704616300927561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8075538557803077533951707 12113307836704616300927561)
      ·
        refine ⟨9084980877528462225695671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113307836704616300927561 9084980877528462225695671)
        ·
          refine ⟨13627471316292693338543507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9084980877528462225695671 13627471316292693338543507)
          ·
            refine ⟨20441206974439040007815261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627471316292693338543507 20441206974439040007815261)
            ·
              refine ⟨7665452615414640002930723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20441206974439040007815261 7665452615414640002930723)
              ·
                refine ⟨11498178923121960004396085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665452615414640002930723 11498178923121960004396085)
                ·
                  refine ⟨1077954274042683750412133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11498178923121960004396085 1077954274042683750412133)
                  ·
                    refine ⟨202116426383003203202275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1077954274042683750412133 202116426383003203202275)
                    ·
                      rfl

theorem cell23_1180861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1180861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180861 prefixEnd_1180861 := by exact prefixLift 1180861
  have htrace : WordTrace (prefixWord ++ tailWord_1180861) baseStart_1180861 baseEnd_1180861 := by
    simpa [prefixWord, tailWord_1180861, baseEnd_1180861] using wordTrace_append hprefix tailTrace_1180861
  have hstable : (prefixWord ++ tailWord_1180861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180861).length < 2 ^ (prefixWord ++ tailWord_1180861).sum := by decide
  have hdescent : baseEnd_1180861 < baseStart_1180861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180865 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1180865 : Nat := 118140960795 + 1180865 * 2 ^ 59
def prefixEnd_1180865 : Nat := 4983230072969 + 3 ^ 40 * 1180865 * 2
def baseEnd_1180865 : Nat := 202117111023875864652269

theorem tailTrace_1180865 : CollatzResearch.WordTrace tailWord_1180865 prefixEnd_1180865 202117111023875864652269 := by
  unfold tailWord_1180865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069684866935255530888049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28713123244623503687258699 43069684866935255530888049)
  ·
    refine ⟨32302263650201441648166037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43069684866935255530888049 32302263650201441648166037)
    ·
      refine ⟨1514168608603192577257783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32302263650201441648166037 1514168608603192577257783)
      ·
        refine ⟨2271252912904788865886675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514168608603192577257783 2271252912904788865886675)
        ·
          refine ⟨3406879369357183298830013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271252912904788865886675 3406879369357183298830013)
          ·
            refine ⟨1277579763508943737061255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3406879369357183298830013 1277579763508943737061255)
            ·
              refine ⟨1916369645263415605591883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277579763508943737061255 1916369645263415605591883)
              ·
                refine ⟨2874554467895123408387825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916369645263415605591883 2874554467895123408387825)
                ·
                  refine ⟨2155915850921342556290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874554467895123408387825 2155915850921342556290869)
                  ·
                    refine ⟨202117111023875864652269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2155915850921342556290869 202117111023875864652269)
                    ·
                      rfl

theorem cell23_1180865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1180865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180865 prefixEnd_1180865 := by exact prefixLift 1180865
  have htrace : WordTrace (prefixWord ++ tailWord_1180865) baseStart_1180865 baseEnd_1180865 := by
    simpa [prefixWord, tailWord_1180865, baseEnd_1180865] using wordTrace_append hprefix tailTrace_1180865
  have hstable : (prefixWord ++ tailWord_1180865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180865).length < 2 ^ (prefixWord ++ tailWord_1180865).sum := by decide
  have hdescent : baseEnd_1180865 < baseStart_1180865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180868 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1180868 : Nat := 118140960795 + 1180868 * 2 ^ 59
def prefixEnd_1180868 : Nat := 4983230072969 + 3 ^ 40 * 1180868 * 2
def baseEnd_1180868 : Nat := 606352873513591082219293

theorem tailTrace_1180868 : CollatzResearch.WordTrace tailWord_1180868 prefixEnd_1180868 606352873513591082219293 := by
  unfold tailWord_1180868
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534897142962193521623629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28713196190616258028831505 21534897142962193521623629)
  ·
    refine ⟨8075586428610822570608861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21534897142962193521623629 8075586428610822570608861)
    ·
      refine ⟨3028344910729058463978323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8075586428610822570608861 3028344910729058463978323)
      ·
        refine ⟨4542517366093587695967485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028344910729058463978323 4542517366093587695967485)
        ·
          refine ⟨1703444012285095385987807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4542517366093587695967485 1703444012285095385987807)
          ·
            refine ⟨2555166018427643078981711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703444012285095385987807 2555166018427643078981711)
            ·
              refine ⟨3832749027641464618472567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555166018427643078981711 3832749027641464618472567)
              ·
                refine ⟨5749123541462196927708851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832749027641464618472567 5749123541462196927708851)
                ·
                  refine ⟨8623685312193295391563277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749123541462196927708851 8623685312193295391563277)
                  ·
                    refine ⟨3233881992072485771836229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8623685312193295391563277 3233881992072485771836229)
                    ·
                      refine ⟨606352873513591082219293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3233881992072485771836229 606352873513591082219293)
                      ·
                        rfl

theorem cell23_1180868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1180868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180868 prefixEnd_1180868 := by exact prefixLift 1180868
  have htrace : WordTrace (prefixWord ++ tailWord_1180868) baseStart_1180868 baseEnd_1180868 := by
    simpa [prefixWord, tailWord_1180868, baseEnd_1180868] using wordTrace_append hprefix tailTrace_1180868
  have hstable : (prefixWord ++ tailWord_1180868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180868).length < 2 ^ (prefixWord ++ tailWord_1180868).sum := by decide
  have hdescent : baseEnd_1180868 < baseStart_1180868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180908 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 6]
def baseStart_1180908 : Nat := 118140960795 + 1180908 * 2 ^ 59
def prefixEnd_1180908 : Nat := 4983230072969 + 3 ^ 40 * 1180908 * 2
def baseEnd_1180908 : Nat := 67374823637752325079901

theorem tailTrace_1180908 : CollatzResearch.WordTrace tailWord_1180908 prefixEnd_1180908 67374823637752325079901 := by
  unfold tailWord_1180908
  simp only [CollatzResearch.WordTrace]
  refine ⟨21535626602889736937351689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28714168803852982583135585 21535626602889736937351689)
  ·
    refine ⟨16151719952167302703013767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21535626602889736937351689 16151719952167302703013767)
    ·
      refine ⟨24227579928250954054520651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16151719952167302703013767 24227579928250954054520651)
      ·
        refine ⟨36341369892376431081780977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24227579928250954054520651 36341369892376431081780977)
        ·
          refine ⟨27256027419282323311335733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36341369892376431081780977 27256027419282323311335733)
          ·
            refine ⟨2555252570557717810437725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27256027419282323311335733 2555252570557717810437725)
            ·
              refine ⟨958219713959144178914147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2555252570557717810437725 958219713959144178914147)
              ·
                refine ⟨1437329570938716268371221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958219713959144178914147 1437329570938716268371221)
                ·
                  refine ⟨67374823637752325079901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1437329570938716268371221 67374823637752325079901)
                  ·
                    rfl

theorem cell23_1180908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_1180908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180908 prefixEnd_1180908 := by exact prefixLift 1180908
  have htrace : WordTrace (prefixWord ++ tailWord_1180908) baseStart_1180908 baseEnd_1180908 := by
    simpa [prefixWord, tailWord_1180908, baseEnd_1180908] using wordTrace_append hprefix tailTrace_1180908
  have hstable : (prefixWord ++ tailWord_1180908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180908).length < 2 ^ (prefixWord ++ tailWord_1180908).sum := by decide
  have hdescent : baseEnd_1180908 < baseStart_1180908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180928 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2]
def baseStart_1180928 : Nat := 118140960795 + 1180928 * 2 ^ 59
def prefixEnd_1180928 : Nat := 4983230072969 + 3 ^ 40 * 1180928 * 2
def baseEnd_1180928 : Nat := 606383682352860847469017

theorem tailTrace_1180928 : CollatzResearch.WordTrace tailWord_1180928 prefixEnd_1180928 606383682352860847469017 := by
  unfold tailWord_1180928
  simp only [CollatzResearch.WordTrace]
  refine ⟨21535991332853508645215719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28714655110471344860287625 21535991332853508645215719)
  ·
    refine ⟨32303986999280262967823579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21535991332853508645215719 32303986999280262967823579)
    ·
      refine ⟨48455980498920394451735369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32303986999280262967823579 48455980498920394451735369)
      ·
        refine ⟨36341985374190295838801527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48455980498920394451735369 36341985374190295838801527)
        ·
          refine ⟨54512978061285443758202291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36341985374190295838801527 54512978061285443758202291)
          ·
            refine ⟨81769467091928165637303437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54512978061285443758202291 81769467091928165637303437)
            ·
              refine ⟨30663550159473062113988789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81769467091928165637303437 30663550159473062113988789)
              ·
                refine ⟨2874707827450599573186449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30663550159473062113988789 2874707827450599573186449)
                ·
                  refine ⟨2156030870587949679889837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874707827450599573186449 2156030870587949679889837)
                  ·
                    refine ⟨808511576470481129958689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156030870587949679889837 808511576470481129958689)
                    ·
                      refine ⟨606383682352860847469017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808511576470481129958689 606383682352860847469017)
                      ·
                        rfl

theorem cell23_1180928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_1180928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180928 prefixEnd_1180928 := by exact prefixLift 1180928
  have htrace : WordTrace (prefixWord ++ tailWord_1180928) baseStart_1180928 baseEnd_1180928 := by
    simpa [prefixWord, tailWord_1180928, baseEnd_1180928] using wordTrace_append hprefix tailTrace_1180928
  have hstable : (prefixWord ++ tailWord_1180928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180928).length < 2 ^ (prefixWord ++ tailWord_1180928).sum := by decide
  have hdescent : baseEnd_1180928 < baseStart_1180928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180946 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1180946 : Nat := 118140960795 + 1180946 * 2 ^ 59
def prefixEnd_1180946 : Nat := 4983230072969 + 3 ^ 40 * 1180946 * 2
def baseEnd_1180946 : Nat := 202130975001547259014645

theorem tailTrace_1180946 : CollatzResearch.WordTrace tailWord_1180946 prefixEnd_1180946 202130975001547259014645 := by
  unfold tailWord_1180946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10768159794910451591146673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28715092786427870909724461 10768159794910451591146673)
  ·
    refine ⟨8076119846182838693360005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10768159794910451591146673 8076119846182838693360005)
    ·
      refine ⟨1514272471159282255005001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8076119846182838693360005 1514272471159282255005001)
      ·
        refine ⟨1135704353369461691253751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514272471159282255005001 1135704353369461691253751)
        ·
          refine ⟨1703556530054192536880627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135704353369461691253751 1703556530054192536880627)
          ·
            refine ⟨2555334795081288805320941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703556530054192536880627 2555334795081288805320941)
            ·
              refine ⟨958250548155483301995353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2555334795081288805320941 958250548155483301995353)
              ·
                refine ⟨718687911116612476496515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958250548155483301995353 718687911116612476496515)
                ·
                  refine ⟨1078031866674918714744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718687911116612476496515 1078031866674918714744773)
                  ·
                    refine ⟨202130975001547259014645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078031866674918714744773 202130975001547259014645)
                    ·
                      rfl

theorem cell23_1180946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1180946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180946 prefixEnd_1180946 := by exact prefixLift 1180946
  have htrace : WordTrace (prefixWord ++ tailWord_1180946) baseStart_1180946 baseEnd_1180946 := by
    simpa [prefixWord, tailWord_1180946, baseEnd_1180946] using wordTrace_append hprefix tailTrace_1180946
  have hstable : (prefixWord ++ tailWord_1180946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180946).length < 2 ^ (prefixWord ++ tailWord_1180946).sum := by decide
  have hdescent : baseEnd_1180946 < baseStart_1180946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180961 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1180961 : Nat := 118140960795 + 1180961 * 2 ^ 59
def prefixEnd_1180961 : Nat := 4983230072969 + 3 ^ 40 * 1180961 * 2
def baseEnd_1180961 : Nat := 606400627214459218356365

theorem tailTrace_1180961 : CollatzResearch.WordTrace tailWord_1180961 prefixEnd_1180961 606400627214459218356365 := by
  unfold tailWord_1180961
  simp only [CollatzResearch.WordTrace]
  refine ⟨43073186274587463926382737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28715457516391642617588491 43073186274587463926382737)
  ·
    refine ⟨32304889705940597944787053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43073186274587463926382737 32304889705940597944787053)
    ·
      refine ⟨12114333639727724229295145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32304889705940597944787053 12114333639727724229295145)
      ·
        refine ⟨9085750229795793171971359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12114333639727724229295145 9085750229795793171971359)
        ·
          refine ⟨13628625344693689757957039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085750229795793171971359 13628625344693689757957039)
          ·
            refine ⟨20442938017040534636935559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628625344693689757957039 20442938017040534636935559)
            ·
              refine ⟨30664407025560801955403339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20442938017040534636935559 30664407025560801955403339)
              ·
                refine ⟨45996610538341202933105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30664407025560801955403339 45996610538341202933105009)
                ·
                  refine ⟨34497457903755902199828757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45996610538341202933105009 34497457903755902199828757)
                  ·
                    refine ⟨1617068339238557915616973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34497457903755902199828757 1617068339238557915616973)
                    ·
                      refine ⟨606400627214459218356365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1617068339238557915616973 606400627214459218356365)
                      ·
                        rfl

theorem cell23_1180961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1180961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180961 prefixEnd_1180961 := by exact prefixLift 1180961
  have htrace : WordTrace (prefixWord ++ tailWord_1180961) baseStart_1180961 baseEnd_1180961 := by
    simpa [prefixWord, tailWord_1180961, baseEnd_1180961] using wordTrace_append hprefix tailTrace_1180961
  have hstable : (prefixWord ++ tailWord_1180961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180961).length < 2 ^ (prefixWord ++ tailWord_1180961).sum := by decide
  have hdescent : baseEnd_1180961 < baseStart_1180961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180981 : List Nat := [1, 3, 3, 1, 2, 2, 2, 9]
def baseStart_1180981 : Nat := 118140960795 + 1180981 * 2 ^ 59
def prefixEnd_1180981 : Nat := 4983230072969 + 3 ^ 40 * 1180981 * 2
def baseEnd_1180981 : Nat := 22459662845464782966899

theorem tailTrace_1180981 : CollatzResearch.WordTrace tailWord_1180981 prefixEnd_1180981 22459662845464782966899 := by
  unfold tailWord_1180981
  simp only [CollatzResearch.WordTrace]
  refine ⟨43073915734515007342110797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28715943823010004894740531 43073915734515007342110797)
  ·
    refine ⟨16152718400443127753291549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43073915734515007342110797 16152718400443127753291549)
    ·
      refine ⟨6057269400166172907484331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16152718400443127753291549 6057269400166172907484331)
      ·
        refine ⟨9085904100249259361226497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057269400166172907484331 9085904100249259361226497)
        ·
          refine ⟨6814428075186944520919873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9085904100249259361226497 6814428075186944520919873)
          ·
            refine ⟨5110821056390208390689905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814428075186944520919873 5110821056390208390689905)
            ·
              refine ⟨3833115792292656293017429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110821056390208390689905 3833115792292656293017429)
              ·
                refine ⟨22459662845464782966899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3833115792292656293017429 22459662845464782966899)
                ·
                  rfl

theorem cell23_1180981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 9].length) (baseStart_1180981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180981 prefixEnd_1180981 := by exact prefixLift 1180981
  have htrace : WordTrace (prefixWord ++ tailWord_1180981) baseStart_1180981 baseEnd_1180981 := by
    simpa [prefixWord, tailWord_1180981, baseEnd_1180981] using wordTrace_append hprefix tailTrace_1180981
  have hstable : (prefixWord ++ tailWord_1180981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180981).length < 2 ^ (prefixWord ++ tailWord_1180981).sum := by decide
  have hdescent : baseEnd_1180981 < baseStart_1180981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180988 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_1180988 : Nat := 118140960795 + 1180988 * 2 ^ 59
def prefixEnd_1180988 : Nat := 4983230072969 + 3 ^ 40 * 1180988 * 2
def baseEnd_1180988 : Nat := 606414491192130612718741

theorem tailTrace_1180988 : CollatzResearch.WordTrace tailWord_1180988 prefixEnd_1180988 606414491192130612718741 := by
  unfold tailWord_1180988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537085522744823768807809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28716114030326431691743745 21537085522744823768807809)
  ·
    refine ⟨16152814142058617826605857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21537085522744823768807809 16152814142058617826605857)
    ·
      refine ⟨12114610606543963369954393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16152814142058617826605857 12114610606543963369954393)
      ·
        refine ⟨9085957954907972527465795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12114610606543963369954393 9085957954907972527465795)
        ·
          refine ⟨13628936932361958791198693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085957954907972527465795 13628936932361958791198693)
          ·
            refine ⟨2555425674817867273349755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13628936932361958791198693 2555425674817867273349755)
            ·
              refine ⟨3833138512226800910024633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555425674817867273349755 3833138512226800910024633)
              ·
                refine ⟨2874853884170100682518475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833138512226800910024633 2874853884170100682518475)
                ·
                  refine ⟨4312280826255151023777713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874853884170100682518475 4312280826255151023777713)
                  ·
                    refine ⟨3234210619691363267833285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312280826255151023777713 3234210619691363267833285)
                    ·
                      refine ⟨606414491192130612718741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3234210619691363267833285 606414491192130612718741)
                      ·
                        rfl

theorem cell23_1180988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_1180988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180988 prefixEnd_1180988 := by exact prefixLift 1180988
  have htrace : WordTrace (prefixWord ++ tailWord_1180988) baseStart_1180988 baseEnd_1180988 := by
    simpa [prefixWord, tailWord_1180988, baseEnd_1180988] using wordTrace_append hprefix tailTrace_1180988
  have hstable : (prefixWord ++ tailWord_1180988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180988).length < 2 ^ (prefixWord ++ tailWord_1180988).sum := by decide
  have hdescent : baseEnd_1180988 < baseStart_1180988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180992 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 1, 2, 2]
def baseStart_1180992 : Nat := 118140960795 + 1180992 * 2 ^ 59
def prefixEnd_1180992 : Nat := 4983230072969 + 3 ^ 40 * 1180992 * 2
def baseEnd_1180992 : Nat := 606416545114748597068723

theorem tailTrace_1180992 : CollatzResearch.WordTrace tailWord_1180992 prefixEnd_1180992 606416545114748597068723 := by
  unfold tailWord_1180992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537158468737578110380615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28716211291650104147174153 21537158468737578110380615)
  ·
    refine ⟨32305737703106367165570923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21537158468737578110380615 32305737703106367165570923)
    ·
      refine ⟨48458606554659550748356385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32305737703106367165570923 48458606554659550748356385)
      ·
        refine ⟨36343954915994663061267289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48458606554659550748356385 36343954915994663061267289)
        ·
          refine ⟨27257966186995997295950467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36343954915994663061267289 27257966186995997295950467)
          ·
            refine ⟨40886949280493995943925701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27257966186995997295950467 40886949280493995943925701)
            ·
              refine ⟨7666302990092624239486069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40886949280493995943925701 7666302990092624239486069)
              ·
                refine ⟨718715905321183522451819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7666302990092624239486069 718715905321183522451819)
                ·
                  refine ⟨1078073857981775283677729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718715905321183522451819 1078073857981775283677729)
                  ·
                    refine ⟨808555393486331462758297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078073857981775283677729 808555393486331462758297)
                    ·
                      refine ⟨606416545114748597068723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808555393486331462758297 606416545114748597068723)
                      ·
                        rfl

theorem cell23_1180992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_1180992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1180992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1180992 prefixEnd_1180992 := by exact prefixLift 1180992
  have htrace : WordTrace (prefixWord ++ tailWord_1180992) baseStart_1180992 baseEnd_1180992 := by
    simpa [prefixWord, tailWord_1180992, baseEnd_1180992] using wordTrace_append hprefix tailTrace_1180992
  have hstable : (prefixWord ++ tailWord_1180992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180992).length < 2 ^ (prefixWord ++ tailWord_1180992).sum := by decide
  have hdescent : baseEnd_1180992 < baseStart_1180992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181051 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_1181051 : Nat := 118140960795 + 1181051 * 2 ^ 59
def prefixEnd_1181051 : Nat := 4983230072969 + 3 ^ 40 * 1181051 * 2
def baseEnd_1181051 : Nat := 606446840473363866230951

theorem tailTrace_1181051 : CollatzResearch.WordTrace tailWord_1181051 prefixEnd_1181051 606446840473363866230951 := by
  unfold tailWord_1181051
  simp only [CollatzResearch.WordTrace]
  refine ⟨43076468844261409297159007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28717645896174272864772671 43076468844261409297159007)
  ·
    refine ⟨64614703266392113945738511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43076468844261409297159007 64614703266392113945738511)
    ·
      refine ⟨96922054899588170918607767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64614703266392113945738511 96922054899588170918607767)
      ·
        refine ⟨145383082349382256377911651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96922054899588170918607767 145383082349382256377911651)
        ·
          refine ⟨218074623524073384566867477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145383082349382256377911651 218074623524073384566867477)
          ·
            refine ⟨10222247977690939901571913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218074623524073384566867477 10222247977690939901571913)
            ·
              refine ⟨7666685983268204926178935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10222247977690939901571913 7666685983268204926178935)
              ·
                refine ⟨11500028974902307389268403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7666685983268204926178935 11500028974902307389268403)
                ·
                  refine ⟨17250043462353461083902605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11500028974902307389268403 17250043462353461083902605)
                  ·
                    refine ⟨6468766298382547906463477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17250043462353461083902605 6468766298382547906463477)
                    ·
                      refine ⟨606446840473363866230951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6468766298382547906463477 606446840473363866230951)
                      ·
                        rfl

theorem cell23_1181051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_1181051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181051 prefixEnd_1181051 := by exact prefixLift 1181051
  have htrace : WordTrace (prefixWord ++ tailWord_1181051) baseStart_1181051 baseEnd_1181051 := by
    simpa [prefixWord, tailWord_1181051, baseEnd_1181051] using wordTrace_append hprefix tailTrace_1181051
  have hstable : (prefixWord ++ tailWord_1181051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181051).length < 2 ^ (prefixWord ++ tailWord_1181051).sum := by decide
  have hdescent : baseEnd_1181051 < baseStart_1181051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181086 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1181086 : Nat := 118140960795 + 1181086 * 2 ^ 59
def prefixEnd_1181086 : Nat := 4983230072969 + 3 ^ 40 * 1181086 * 2
def baseEnd_1181086 : Nat := 606464812296271229293291

theorem tailTrace_1181086 : CollatzResearch.WordTrace tailWord_1181086 prefixEnd_1181086 606464812296271229293291 := by
  unfold tailWord_1181086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5384718174891826284335389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28718496932756406849788741 5384718174891826284335389)
  ·
    refine ⟨2019269315584434856625771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5384718174891826284335389 2019269315584434856625771)
    ·
      refine ⟨3028903973376652284938657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019269315584434856625771 3028903973376652284938657)
      ·
        refine ⟨2271677980032489213703993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028903973376652284938657 2271677980032489213703993)
        ·
          refine ⟨1703758485024366910277995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271677980032489213703993 1703758485024366910277995)
          ·
            refine ⟨2555637727536550365416993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703758485024366910277995 2555637727536550365416993)
            ·
              refine ⟨1916728295652412774062745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555637727536550365416993 1916728295652412774062745)
              ·
                refine ⟨1437546221739309580547059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916728295652412774062745 1437546221739309580547059)
                ·
                  refine ⟨2156319332608964370820589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437546221739309580547059 2156319332608964370820589)
                  ·
                    refine ⟨808619749728361639057721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156319332608964370820589 808619749728361639057721)
                    ·
                      refine ⟨606464812296271229293291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808619749728361639057721 606464812296271229293291)
                      ·
                        rfl

theorem cell23_1181086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1181086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181086 prefixEnd_1181086 := by exact prefixLift 1181086
  have htrace : WordTrace (prefixWord ++ tailWord_1181086) baseStart_1181086 baseEnd_1181086 := by
    simpa [prefixWord, tailWord_1181086, baseEnd_1181086] using wordTrace_append hprefix tailTrace_1181086
  have hstable : (prefixWord ++ tailWord_1181086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181086).length < 2 ^ (prefixWord ++ tailWord_1181086).sum := by decide
  have hdescent : baseEnd_1181086 < baseStart_1181086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181128 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1181128 : Nat := 118140960795 + 1181128 * 2 ^ 59
def prefixEnd_1181128 : Nat := 4983230072969 + 3 ^ 40 * 1181128 * 2
def baseEnd_1181128 : Nat := 606486378483760064968097

theorem tailTrace_1181128 : CollatzResearch.WordTrace tailWord_1181128 prefixEnd_1181128 606486378483760064968097 := by
  unfold tailWord_1181128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539638632491225723856019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28719518176654967631808025 21539638632491225723856019)
  ·
    refine ⟨32309457948736838585784029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21539638632491225723856019 32309457948736838585784029)
    ·
      refine ⟨12116046730776314469669011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32309457948736838585784029 12116046730776314469669011)
      ·
        refine ⟨18174070096164471704503517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12116046730776314469669011 18174070096164471704503517)
        ·
          refine ⟨6815276286061676889188819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18174070096164471704503517 6815276286061676889188819)
          ·
            refine ⟨10222914429092515333783229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6815276286061676889188819 10222914429092515333783229)
            ·
              refine ⟨3833592910909693250168711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10222914429092515333783229 3833592910909693250168711)
              ·
                refine ⟨5750389366364539875253067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833592910909693250168711 5750389366364539875253067)
                ·
                  refine ⟨8625584049546809812879601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5750389366364539875253067 8625584049546809812879601)
                  ·
                    refine ⟨6469188037160107359659701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8625584049546809812879601 6469188037160107359659701)
                    ·
                      refine ⟨606486378483760064968097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6469188037160107359659701 606486378483760064968097)
                      ·
                        rfl

theorem cell23_1181128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1181128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181128 prefixEnd_1181128 := by exact prefixLift 1181128
  have htrace : WordTrace (prefixWord ++ tailWord_1181128) baseStart_1181128 baseEnd_1181128 := by
    simpa [prefixWord, tailWord_1181128, baseEnd_1181128] using wordTrace_append hprefix tailTrace_1181128
  have hstable : (prefixWord ++ tailWord_1181128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181128).length < 2 ^ (prefixWord ++ tailWord_1181128).sum := by decide
  have hdescent : baseEnd_1181128 < baseStart_1181128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181155 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1181155 : Nat := 118140960795 + 1181155 * 2 ^ 59
def prefixEnd_1181155 : Nat := 4983230072969 + 3 ^ 40 * 1181155 * 2
def baseEnd_1181155 : Nat := 606500242461431459330473

theorem tailTrace_1181155 : CollatzResearch.WordTrace tailWord_1181155 prefixEnd_1181155 606500242461431459330473 := by
  unfold tailWord_1181155
  simp only [CollatzResearch.WordTrace]
  refine ⟨43080262035884635058944919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28720174690589756705963279 43080262035884635058944919)
  ·
    refine ⟨64620393053826952588417379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43080262035884635058944919 64620393053826952588417379)
    ·
      refine ⟨96930589580740428882626069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64620393053826952588417379 96930589580740428882626069)
      ·
        refine ⟨4543621386597207603873097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96930589580740428882626069 4543621386597207603873097)
        ·
          refine ⟨3407716039947905702904823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4543621386597207603873097 3407716039947905702904823)
          ·
            refine ⟨5111574059921858554357235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407716039947905702904823 5111574059921858554357235)
            ·
              refine ⟨7667361089882787831535853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111574059921858554357235 7667361089882787831535853)
              ·
                refine ⟨2875260408706045436825945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7667361089882787831535853 2875260408706045436825945)
                ·
                  refine ⟨2156445306529534077619459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875260408706045436825945 2156445306529534077619459)
                  ·
                    refine ⟨3234667959794301116429189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2156445306529534077619459 3234667959794301116429189)
                    ·
                      refine ⟨606500242461431459330473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3234667959794301116429189 606500242461431459330473)
                      ·
                        rfl

theorem cell23_1181155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1181155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181155 prefixEnd_1181155 := by exact prefixLift 1181155
  have htrace : WordTrace (prefixWord ++ tailWord_1181155) baseStart_1181155 baseEnd_1181155 := by
    simpa [prefixWord, tailWord_1181155, baseEnd_1181155] using wordTrace_append hprefix tailTrace_1181155
  have hstable : (prefixWord ++ tailWord_1181155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181155).length < 2 ^ (prefixWord ++ tailWord_1181155).sum := by decide
  have hdescent : baseEnd_1181155 < baseStart_1181155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181239 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_1181239 : Nat := 118140960795 + 1181239 * 2 ^ 59
def prefixEnd_1181239 : Nat := 4983230072969 + 3 ^ 40 * 1181239 * 2
def baseEnd_1181239 : Nat := 606543374836409130680087

theorem tailTrace_1181239 : CollatzResearch.WordTrace tailWord_1181239 prefixEnd_1181239 606543374836409130680087 := by
  unfold tailWord_1181239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083325767580317405002771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28722217178386878270001847 43083325767580317405002771)
  ·
    refine ⟨64624988651370476107504157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43083325767580317405002771 64624988651370476107504157)
    ·
      refine ⟨24234370744263928540314059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64624988651370476107504157 24234370744263928540314059)
      ·
        refine ⟨36351556116395892810471089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24234370744263928540314059 36351556116395892810471089)
        ·
          refine ⟨27263667087296919607853317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36351556116395892810471089 27263667087296919607853317)
          ·
            refine ⟨5111937578868172426472497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27263667087296919607853317 5111937578868172426472497)
            ·
              refine ⟨3833953184151129319854373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5111937578868172426472497 3833953184151129319854373)
              ·
                refine ⟨718866222028336747472695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3833953184151129319854373 718866222028336747472695)
                ·
                  refine ⟨1078299333042505121209043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 718866222028336747472695 1078299333042505121209043)
                  ·
                    refine ⟨1617448999563757681813565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1078299333042505121209043 1617448999563757681813565)
                    ·
                      refine ⟨606543374836409130680087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1617448999563757681813565 606543374836409130680087)
                      ·
                        rfl

theorem cell23_1181239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_1181239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181239 prefixEnd_1181239 := by exact prefixLift 1181239
  have htrace : WordTrace (prefixWord ++ tailWord_1181239) baseStart_1181239 baseEnd_1181239 := by
    simpa [prefixWord, tailWord_1181239, baseEnd_1181239] using wordTrace_append hprefix tailTrace_1181239
  have hstable : (prefixWord ++ tailWord_1181239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181239).length < 2 ^ (prefixWord ++ tailWord_1181239).sum := by decide
  have hdescent : baseEnd_1181239 < baseStart_1181239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181285 : List Nat := [1, 3, 1, 3, 3, 3, 9]
def baseStart_1181285 : Nat := 118140960795 + 1181285 * 2 ^ 59
def prefixEnd_1181285 : Nat := 4983230072969 + 3 ^ 40 * 1181285 * 2
def baseEnd_1181285 : Nat := 7488481419092789514875

theorem tailTrace_1181285 : CollatzResearch.WordTrace tailWord_1181285 prefixEnd_1181285 7488481419092789514875 := by
  unfold tailWord_1181285
  simp only [CollatzResearch.WordTrace]
  refine ⟨43085003525413667261177309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28723335683609111507451539 43085003525413667261177309)
  ·
    refine ⟨16156876322030125222941491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43085003525413667261177309 16156876322030125222941491)
    ·
      refine ⟨24235314483045187834412237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16156876322030125222941491 24235314483045187834412237)
      ·
        refine ⟨9088242931141945437904589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24235314483045187834412237 9088242931141945437904589)
        ·
          refine ⟨3408091099178229539214221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9088242931141945437904589 3408091099178229539214221)
          ·
            refine ⟨1278034162191836077205333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3408091099178229539214221 1278034162191836077205333)
            ·
              refine ⟨7488481419092789514875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1278034162191836077205333 7488481419092789514875)
              ·
                rfl

theorem cell23_1181285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 9].length) (baseStart_1181285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181285 prefixEnd_1181285 := by exact prefixLift 1181285
  have htrace : WordTrace (prefixWord ++ tailWord_1181285) baseStart_1181285 baseEnd_1181285 := by
    simpa [prefixWord, tailWord_1181285, baseEnd_1181285] using wordTrace_append hprefix tailTrace_1181285
  have hstable : (prefixWord ++ tailWord_1181285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181285).length < 2 ^ (prefixWord ++ tailWord_1181285).sum := by decide
  have hdescent : baseEnd_1181285 < baseStart_1181285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181296 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2]
def baseStart_1181296 : Nat := 118140960795 + 1181296 * 2 ^ 59
def prefixEnd_1181296 : Nat := 4983230072969 + 3 ^ 40 * 1181296 * 2
def baseEnd_1181296 : Nat := 606572643233715407667325

theorem tailTrace_1181296 : CollatzResearch.WordTrace tailWord_1181296 prefixEnd_1181296 606572643233715407667325 := by
  unfold tailWord_1181296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542702364186908069913871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28723603152249210759885161 21542702364186908069913871)
  ·
    refine ⟨32314053546280362104870807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21542702364186908069913871 32314053546280362104870807)
    ·
      refine ⟨48471080319420543157306211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32314053546280362104870807 48471080319420543157306211)
      ·
        refine ⟨72706620479130814735959317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48471080319420543157306211 72706620479130814735959317)
        ·
          refine ⟨3408122834959256940748093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72706620479130814735959317 3408122834959256940748093)
          ·
            refine ⟨1278046063109721352780535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3408122834959256940748093 1278046063109721352780535)
            ·
              refine ⟨1917069094664582029170803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278046063109721352780535 1917069094664582029170803)
              ·
                refine ⟨2875603641996873043756205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917069094664582029170803 2875603641996873043756205)
                ·
                  refine ⟨1078351365748827391408577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2875603641996873043756205 1078351365748827391408577)
                  ·
                    refine ⟨808763524311620543556433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078351365748827391408577 808763524311620543556433)
                    ·
                      refine ⟨606572643233715407667325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808763524311620543556433 606572643233715407667325)
                      ·
                        rfl

theorem cell23_1181296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 2, 2].length) (baseStart_1181296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181296 prefixEnd_1181296 := by exact prefixLift 1181296
  have htrace : WordTrace (prefixWord ++ tailWord_1181296) baseStart_1181296 baseEnd_1181296 := by
    simpa [prefixWord, tailWord_1181296, baseEnd_1181296] using wordTrace_append hprefix tailTrace_1181296
  have hstable : (prefixWord ++ tailWord_1181296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181296).length < 2 ^ (prefixWord ++ tailWord_1181296).sum := by decide
  have hdescent : baseEnd_1181296 < baseStart_1181296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181302 : List Nat := [5, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1181302 : Nat := 118140960795 + 1181302 * 2 ^ 59
def prefixEnd_1181302 : Nat := 4983230072969 + 3 ^ 40 * 1181302 * 2
def baseEnd_1181302 : Nat := 22465767559912680896011

theorem tailTrace_1181302 : CollatzResearch.WordTrace tailWord_1181302 prefixEnd_1181302 22465767559912680896011 := by
  unfold tailWord_1181302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692851472897004947784135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28723749044234719443030773 2692851472897004947784135)
  ·
    refine ⟨4039277209345507421676203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692851472897004947784135 4039277209345507421676203)
    ·
      refine ⟨6058915814018261132514305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039277209345507421676203 6058915814018261132514305)
      ·
        refine ⟨4544186860513695849385729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6058915814018261132514305 4544186860513695849385729)
        ·
          refine ⟨3408140145385271887039297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4544186860513695849385729 3408140145385271887039297)
          ·
            refine ⟨2556105109038953915279473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408140145385271887039297 2556105109038953915279473)
            ·
              refine ⟨1917078831779215436459605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556105109038953915279473 1917078831779215436459605)
              ·
                refine ⟨22465767559912680896011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1917078831779215436459605 22465767559912680896011)
                ·
                  rfl

theorem cell23_1181302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1181302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181302 prefixEnd_1181302 := by exact prefixLift 1181302
  have htrace : WordTrace (prefixWord ++ tailWord_1181302) baseStart_1181302 baseEnd_1181302 := by
    simpa [prefixWord, tailWord_1181302, baseEnd_1181302] using wordTrace_append hprefix tailTrace_1181302
  have hstable : (prefixWord ++ tailWord_1181302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181302).length < 2 ^ (prefixWord ++ tailWord_1181302).sum := by decide
  have hdescent : baseEnd_1181302 < baseStart_1181302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181316 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1181316 : Nat := 118140960795 + 1181316 * 2 ^ 59
def prefixEnd_1181316 : Nat := 4983230072969 + 3 ^ 40 * 1181316 * 2
def baseEnd_1181316 : Nat := 606582912846805329417233

theorem tailTrace_1181316 : CollatzResearch.WordTrace tailWord_1181316 prefixEnd_1181316 606582912846805329417233 := by
  unfold tailWord_1181316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543067094150679777777901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28724089458867573037037201 21543067094150679777777901)
  ·
    refine ⟨8078650160306504916666713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21543067094150679777777901 8078650160306504916666713)
    ·
      refine ⟨6058987620229878687500035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8078650160306504916666713 6058987620229878687500035)
      ·
        refine ⟨9088481430344818031250053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058987620229878687500035 9088481430344818031250053)
        ·
          refine ⟨1704090268189653380859385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9088481430344818031250053 1704090268189653380859385)
          ·
            refine ⟨1278067701142240035644539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704090268189653380859385 1278067701142240035644539)
            ·
              refine ⟨1917101551713360053466809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278067701142240035644539 1917101551713360053466809)
              ·
                refine ⟨1437826163785020040100107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917101551713360053466809 1437826163785020040100107)
                ·
                  refine ⟨2156739245677530060150161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437826163785020040100107 2156739245677530060150161)
                  ·
                    refine ⟨1617554434258147545112621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156739245677530060150161 1617554434258147545112621)
                    ·
                      refine ⟨606582912846805329417233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1617554434258147545112621 606582912846805329417233)
                      ·
                        rfl

theorem cell23_1181316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1181316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181316 prefixEnd_1181316 := by exact prefixLift 1181316
  have htrace : WordTrace (prefixWord ++ tailWord_1181316) baseStart_1181316 baseEnd_1181316 := by
    simpa [prefixWord, tailWord_1181316, baseEnd_1181316] using wordTrace_append hprefix tailTrace_1181316
  have hstable : (prefixWord ++ tailWord_1181316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181316).length < 2 ^ (prefixWord ++ tailWord_1181316).sum := by decide
  have hdescent : baseEnd_1181316 < baseStart_1181316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181375 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 7]
def baseStart_1181375 : Nat := 118140960795 + 1181375 * 2 ^ 59
def prefixEnd_1181375 : Nat := 4983230072969 + 3 ^ 40 * 1181375 * 2
def baseEnd_1181375 : Nat := 67401467578380066508829

theorem tailTrace_1181375 : CollatzResearch.WordTrace tailWord_1181375 prefixEnd_1181375 67401467578380066508829 := by
  unfold tailWord_1181375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43088286095087612631953579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28725524063391741754635719 43088286095087612631953579)
  ·
    refine ⟨64632429142631418947930369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43088286095087612631953579 64632429142631418947930369)
    ·
      refine ⟨48474321856973564210947777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64632429142631418947930369 48474321856973564210947777)
      ·
        refine ⟨36355741392730173158210833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48474321856973564210947777 36355741392730173158210833)
        ·
          refine ⟨27266806044547629868658125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36355741392730173158210833 27266806044547629868658125)
          ·
            refine ⟨10225052266705361200746797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27266806044547629868658125 10225052266705361200746797)
            ·
              refine ⟨3834394600014510450280049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10225052266705361200746797 3834394600014510450280049)
              ·
                refine ⟨2875795950010882837710037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834394600014510450280049 2875795950010882837710037)
                ·
                  refine ⟨67401467578380066508829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2875795950010882837710037 67401467578380066508829)
                  ·
                    rfl

theorem cell23_1181375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 7].length) (baseStart_1181375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181375 prefixEnd_1181375 := by exact prefixLift 1181375
  have htrace : WordTrace (prefixWord ++ tailWord_1181375) baseStart_1181375 baseEnd_1181375 := by
    simpa [prefixWord, tailWord_1181375, baseEnd_1181375] using wordTrace_append hprefix tailTrace_1181375
  have hstable : (prefixWord ++ tailWord_1181375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181375).length < 2 ^ (prefixWord ++ tailWord_1181375).sum := by decide
  have hdescent : baseEnd_1181375 < baseStart_1181375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181402 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1181402 : Nat := 118140960795 + 1181402 * 2 ^ 59
def prefixEnd_1181402 : Nat := 4983230072969 + 3 ^ 40 * 1181402 * 2
def baseEnd_1181402 : Nat := 606627072183091992941837

theorem tailTrace_1181402 : CollatzResearch.WordTrace tailWord_1181402 prefixEnd_1181402 606627072183091992941837 := by
  unfold tailWord_1181402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772317716497449060796615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28726180577326530828790973 10772317716497449060796615)
  ·
    refine ⟨16158476574746173591194923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10772317716497449060796615 16158476574746173591194923)
    ·
      refine ⟨24237714862119260386792385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16158476574746173591194923 24237714862119260386792385)
      ·
        refine ⟨18178286146589445290094289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24237714862119260386792385 18178286146589445290094289)
        ·
          refine ⟨13633714609942083967570717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18178286146589445290094289 13633714609942083967570717)
          ·
            refine ⟨5112642978728281487839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13633714609942083967570717 5112642978728281487839019)
            ·
              refine ⟨7668964468092422231758529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112642978728281487839019 7668964468092422231758529)
              ·
                refine ⟨5751723351069316673818897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7668964468092422231758529 5751723351069316673818897)
                ·
                  refine ⟨4313792513301987505364173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751723351069316673818897 4313792513301987505364173)
                  ·
                    refine ⟨1617672192488245314511565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4313792513301987505364173 1617672192488245314511565)
                    ·
                      refine ⟨606627072183091992941837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1617672192488245314511565 606627072183091992941837)
                      ·
                        rfl

theorem cell23_1181402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1181402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181402 prefixEnd_1181402 := by exact prefixLift 1181402
  have htrace : WordTrace (prefixWord ++ tailWord_1181402) baseStart_1181402 baseEnd_1181402 := by
    simpa [prefixWord, tailWord_1181402, baseEnd_1181402] using wordTrace_append hprefix tailTrace_1181402
  have hstable : (prefixWord ++ tailWord_1181402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181402).length < 2 ^ (prefixWord ++ tailWord_1181402).sum := by decide
  have hdescent : baseEnd_1181402 < baseStart_1181402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181445 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_1181445 : Nat := 118140960795 + 1181445 * 2 ^ 59
def prefixEnd_1181445 : Nat := 4983230072969 + 3 ^ 40 * 1181445 * 2
def baseEnd_1181445 : Nat := 606649151851235324704139

theorem tailTrace_1181445 : CollatzResearch.WordTrace tailWord_1181445 prefixEnd_1181445 606649151851235324704139 := by
  unfold tailWord_1181445
  simp only [CollatzResearch.WordTrace]
  refine ⟨43090839204834014587001789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28727226136556009724667859 43090839204834014587001789)
  ·
    refine ⟨16159064701812755470125671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43090839204834014587001789 16159064701812755470125671)
    ·
      refine ⟨24238597052719133205188507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16159064701812755470125671 24238597052719133205188507)
      ·
        refine ⟨36357895579078699807782761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24238597052719133205188507 36357895579078699807782761)
        ·
          refine ⟨27268421684309024855837071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36357895579078699807782761 27268421684309024855837071)
          ·
            refine ⟨40902632526463537283755607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27268421684309024855837071 40902632526463537283755607)
            ·
              refine ⟨61353948789695305925633411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40902632526463537283755607 61353948789695305925633411)
              ·
                refine ⟨92030923184542958888450117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61353948789695305925633411 92030923184542958888450117)
                ·
                  refine ⟨17255798097101804791584397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92030923184542958888450117 17255798097101804791584397)
                  ·
                    refine ⟨6470924286413176796844149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17255798097101804791584397 6470924286413176796844149)
                    ·
                      refine ⟨606649151851235324704139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6470924286413176796844149 606649151851235324704139)
                      ·
                        rfl

theorem cell23_1181445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_1181445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181445 prefixEnd_1181445 := by exact prefixLift 1181445
  have htrace : WordTrace (prefixWord ++ tailWord_1181445) baseStart_1181445 baseEnd_1181445 := by
    simpa [prefixWord, tailWord_1181445, baseEnd_1181445] using wordTrace_append hprefix tailTrace_1181445
  have hstable : (prefixWord ++ tailWord_1181445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181445).length < 2 ^ (prefixWord ++ tailWord_1181445).sum := by decide
  have hdescent : baseEnd_1181445 < baseStart_1181445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181452 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_1181452 : Nat := 118140960795 + 1181452 * 2 ^ 59
def prefixEnd_1181452 : Nat := 4983230072969 + 3 ^ 40 * 1181452 * 2
def baseEnd_1181452 : Nat := 202217582071938932438869

theorem tailTrace_1181452 : CollatzResearch.WordTrace tailWord_1181452 prefixEnd_1181452 202217582071938932438869 := by
  unfold tailWord_1181452
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545547257904327391253305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28727396343872436521671073 21545547257904327391253305)
  ·
    refine ⟨16159160443428245543439979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21545547257904327391253305 16159160443428245543439979)
    ·
      refine ⟨24238740665142368315159969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16159160443428245543439979 24238740665142368315159969)
      ·
        refine ⟨18179055498856776236369977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24238740665142368315159969 18179055498856776236369977)
        ·
          refine ⟨13634291624142582177277483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18179055498856776236369977 13634291624142582177277483)
          ·
            refine ⟨20451437436213873265916225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13634291624142582177277483 20451437436213873265916225)
            ·
              refine ⟨15338578077160404949437169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20451437436213873265916225 15338578077160404949437169)
              ·
                refine ⟨11503933557870303712077877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15338578077160404949437169 11503933557870303712077877)
                ·
                  refine ⟨1078493771050340973007301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11503933557870303712077877 1078493771050340973007301)
                  ·
                    refine ⟨202217582071938932438869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078493771050340973007301 202217582071938932438869)
                    ·
                      rfl

theorem cell23_1181452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_1181452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181452 prefixEnd_1181452 := by exact prefixLift 1181452
  have htrace : WordTrace (prefixWord ++ tailWord_1181452) baseStart_1181452 baseEnd_1181452 := by
    simpa [prefixWord, tailWord_1181452, baseEnd_1181452] using wordTrace_append hprefix tailTrace_1181452
  have hstable : (prefixWord ++ tailWord_1181452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181452).length < 2 ^ (prefixWord ++ tailWord_1181452).sum := by decide
  have hdescent : baseEnd_1181452 < baseStart_1181452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181455 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_1181455 : Nat := 118140960795 + 1181455 * 2 ^ 59
def prefixEnd_1181455 : Nat := 4983230072969 + 3 ^ 40 * 1181455 * 2
def baseEnd_1181455 : Nat := 606654286657780285579093

theorem tailTrace_1181455 : CollatzResearch.WordTrace tailWord_1181455 prefixEnd_1181455 606654286657780285579093 := by
  unfold tailWord_1181455
  simp only [CollatzResearch.WordTrace]
  refine ⟨43091203934797786294865819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28727469289865190863243879 43091203934797786294865819)
  ·
    refine ⟨64636805902196679442298729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43091203934797786294865819 64636805902196679442298729)
    ·
      refine ⟨48477604426647509581724047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64636805902196679442298729 48477604426647509581724047)
      ·
        refine ⟨72716406639971264372586071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48477604426647509581724047 72716406639971264372586071)
        ·
          refine ⟨109074609959956896558879107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72716406639971264372586071 109074609959956896558879107)
          ·
            refine ⟨163611914939935344838318661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109074609959956896558879107 163611914939935344838318661)
            ·
              refine ⟨30677234051237877157184749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163611914939935344838318661 30677234051237877157184749)
              ·
                refine ⟨11503962769214203933944281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30677234051237877157184749 11503962769214203933944281)
                ·
                  refine ⟨8627972076910652950458211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11503962769214203933944281 8627972076910652950458211)
                  ·
                    refine ⟨12941958115365979425687317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8627972076910652950458211 12941958115365979425687317)
                    ·
                      refine ⟨606654286657780285579093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12941958115365979425687317 606654286657780285579093)
                      ·
                        rfl

theorem cell23_1181455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_1181455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181455 prefixEnd_1181455 := by exact prefixLift 1181455
  have htrace : WordTrace (prefixWord ++ tailWord_1181455) baseStart_1181455 baseEnd_1181455 := by
    simpa [prefixWord, tailWord_1181455, baseEnd_1181455] using wordTrace_append hprefix tailTrace_1181455
  have hstable : (prefixWord ++ tailWord_1181455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181455).length < 2 ^ (prefixWord ++ tailWord_1181455).sum := by decide
  have hdescent : baseEnd_1181455 < baseStart_1181455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181460 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1181460 : Nat := 118140960795 + 1181460 * 2 ^ 59
def prefixEnd_1181460 : Nat := 4983230072969 + 3 ^ 40 * 1181460 * 2
def baseEnd_1181460 : Nat := 67406317117894751779619

theorem tailTrace_1181460 : CollatzResearch.WordTrace tailWord_1181460 prefixEnd_1181460 67406317117894751779619 := by
  unfold tailWord_1181460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545693149889836074398917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28727590866519781432531889 21545693149889836074398917)
  ·
    refine ⟨4039817465604344263949797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21545693149889836074398917 4039817465604344263949797)
    ·
      refine ⟨757465774800814549490587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4039817465604344263949797 757465774800814549490587)
      ·
        refine ⟨1136198662201221824235881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757465774800814549490587 1136198662201221824235881)
        ·
          refine ⟨852148996650916368176911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136198662201221824235881 852148996650916368176911)
          ·
            refine ⟨1278223494976374552265367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852148996650916368176911 1278223494976374552265367)
            ·
              refine ⟨1917335242464561828398051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278223494976374552265367 1917335242464561828398051)
              ·
                refine ⟨2876002863696842742597077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917335242464561828398051 2876002863696842742597077)
                ·
                  refine ⟨67406317117894751779619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2876002863696842742597077 67406317117894751779619)
                  ·
                    rfl

theorem cell23_1181460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1181460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181460 prefixEnd_1181460 := by exact prefixLift 1181460
  have htrace : WordTrace (prefixWord ++ tailWord_1181460) baseStart_1181460 baseEnd_1181460 := by
    simpa [prefixWord, tailWord_1181460, baseEnd_1181460] using wordTrace_append hprefix tailTrace_1181460
  have hstable : (prefixWord ++ tailWord_1181460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181460).length < 2 ^ (prefixWord ++ tailWord_1181460).sum := by decide
  have hdescent : baseEnd_1181460 < baseStart_1181460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181549 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1181549 : Nat := 118140960795 + 1181549 * 2 ^ 59
def prefixEnd_1181549 : Nat := 4983230072969 + 3 ^ 40 * 1181549 * 2
def baseEnd_1181549 : Nat := 606702553839302917803661

theorem tailTrace_1181549 : CollatzResearch.WordTrace tailWord_1181549 prefixEnd_1181549 606702553839302917803661 := by
  unfold tailWord_1181549
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094632396457240348787701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28729754930971493565858467 43094632396457240348787701)
  ·
    refine ⟨4040121787167866282698847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43094632396457240348787701 4040121787167866282698847)
    ·
      refine ⟨6060182680751799424048271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040121787167866282698847 6060182680751799424048271)
      ·
        refine ⟨9090274021127699136072407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060182680751799424048271 9090274021127699136072407)
        ·
          refine ⟨13635411031691548704108611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090274021127699136072407 13635411031691548704108611)
          ·
            refine ⟨20453116547537323056162917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13635411031691548704108611 20453116547537323056162917)
            ·
              refine ⟨3834959352663248073030547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20453116547537323056162917 3834959352663248073030547)
              ·
                refine ⟨5752439028994872109545821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834959352663248073030547 5752439028994872109545821)
                ·
                  refine ⟨2157164635873077041079683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5752439028994872109545821 2157164635873077041079683)
                  ·
                    refine ⟨3235746953809615561619525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2157164635873077041079683 3235746953809615561619525)
                    ·
                      refine ⟨606702553839302917803661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3235746953809615561619525 606702553839302917803661)
                      ·
                        rfl

theorem cell23_1181549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1181549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181549 prefixEnd_1181549 := by exact prefixLift 1181549
  have htrace : WordTrace (prefixWord ++ tailWord_1181549) baseStart_1181549 baseEnd_1181549 := by
    simpa [prefixWord, tailWord_1181549, baseEnd_1181549] using wordTrace_append hprefix tailTrace_1181549
  have hstable : (prefixWord ++ tailWord_1181549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181549).length < 2 ^ (prefixWord ++ tailWord_1181549).sum := by decide
  have hdescent : baseEnd_1181549 < baseStart_1181549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181576 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1181576 : Nat := 118140960795 + 1181576 * 2 ^ 59
def prefixEnd_1181576 : Nat := 4983230072969 + 3 ^ 40 * 1181576 * 2
def baseEnd_1181576 : Nat := 202238805938991437388679

theorem tailTrace_1181576 : CollatzResearch.WordTrace tailWord_1181576 prefixEnd_1181576 202238805938991437388679 := by
  unfold tailWord_1181576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21547808583679711980010291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28730411444906282640013721 21547808583679711980010291)
  ·
    refine ⟨32321712875519567970015437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21547808583679711980010291 32321712875519567970015437)
    ·
      refine ⟨12120642328319837988755789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32321712875519567970015437 12120642328319837988755789)
      ·
        refine ⟨4545240873119939245783421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12120642328319837988755789 4545240873119939245783421)
        ·
          refine ⟨1704465327419977217168783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4545240873119939245783421 1704465327419977217168783)
          ·
            refine ⟨2556697991129965825753175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704465327419977217168783 2556697991129965825753175)
            ·
              refine ⟨3835046986694948738629763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556697991129965825753175 3835046986694948738629763)
              ·
                refine ⟨5752570480042423107944645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835046986694948738629763 5752570480042423107944645)
                ·
                  refine ⟨1078606965007954332739621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5752570480042423107944645 1078606965007954332739621)
                  ·
                    refine ⟨202238805938991437388679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078606965007954332739621 202238805938991437388679)
                    ·
                      rfl

theorem cell23_1181576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1181576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181576 prefixEnd_1181576 := by exact prefixLift 1181576
  have htrace : WordTrace (prefixWord ++ tailWord_1181576) baseStart_1181576 baseEnd_1181576 := by
    simpa [prefixWord, tailWord_1181576, baseEnd_1181576] using wordTrace_append hprefix tailTrace_1181576
  have hstable : (prefixWord ++ tailWord_1181576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181576).length < 2 ^ (prefixWord ++ tailWord_1181576).sum := by decide
  have hdescent : baseEnd_1181576 < baseStart_1181576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181586 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1181586 : Nat := 118140960795 + 1181586 * 2 ^ 59
def prefixEnd_1181586 : Nat := 4983230072969 + 3 ^ 40 * 1181586 * 2
def baseEnd_1181586 : Nat := 606721552623519273040991

theorem tailTrace_1181586 : CollatzResearch.WordTrace tailWord_1181586 prefixEnd_1181586 606721552623519273040991 := by
  unfold tailWord_1181586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10773995474330798916971153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28730654598215463778589741 10773995474330798916971153)
  ·
    refine ⟨8080496605748099187728365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10773995474330798916971153 8080496605748099187728365)
    ·
      refine ⟨3030186227155537195398137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8080496605748099187728365 3030186227155537195398137)
      ·
        refine ⟨2272639670366652896548603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3030186227155537195398137 2272639670366652896548603)
        ·
          refine ⟨3408959505549979344822905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272639670366652896548603 3408959505549979344822905)
          ·
            refine ⟨2556719629162484508617179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408959505549979344822905 2556719629162484508617179)
            ·
              refine ⟨3835079443743726762925769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556719629162484508617179 3835079443743726762925769)
              ·
                refine ⟨2876309582807795072194327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835079443743726762925769 2876309582807795072194327)
                ·
                  refine ⟨4314464374211692608291491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876309582807795072194327 4314464374211692608291491)
                  ·
                    refine ⟨6471696561317538912437237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314464374211692608291491 6471696561317538912437237)
                    ·
                      refine ⟨606721552623519273040991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6471696561317538912437237 606721552623519273040991)
                      ·
                        rfl

theorem cell23_1181586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1181586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181586 prefixEnd_1181586 := by exact prefixLift 1181586
  have htrace : WordTrace (prefixWord ++ tailWord_1181586) baseStart_1181586 baseEnd_1181586 := by
    simpa [prefixWord, tailWord_1181586, baseEnd_1181586] using wordTrace_append hprefix tailTrace_1181586
  have hstable : (prefixWord ++ tailWord_1181586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181586).length < 2 ^ (prefixWord ++ tailWord_1181586).sum := by decide
  have hdescent : baseEnd_1181586 < baseStart_1181586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181596 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1181596 : Nat := 118140960795 + 1181596 * 2 ^ 59
def prefixEnd_1181596 : Nat := 4983230072969 + 3 ^ 40 * 1181596 * 2
def baseEnd_1181596 : Nat := 606726687430064233915945

theorem tailTrace_1181596 : CollatzResearch.WordTrace tailWord_1181596 prefixEnd_1181596 606726687430064233915945 := by
  unfold tailWord_1181596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21548173313643483687874321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28730897751524644917165761 21548173313643483687874321)
  ·
    refine ⟨16161129985232612765905741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21548173313643483687874321 16161129985232612765905741)
    ·
      refine ⟨6060423744462229787214653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16161129985232612765905741 6060423744462229787214653)
      ·
        refine ⟨2272658904173336170205495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6060423744462229787214653 2272658904173336170205495)
        ·
          refine ⟨3408988356260004255308243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272658904173336170205495 3408988356260004255308243)
          ·
            refine ⟨5113482534390006382962365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408988356260004255308243 5113482534390006382962365)
            ·
              refine ⟨1917555950396252393610887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5113482534390006382962365 1917555950396252393610887)
              ·
                refine ⟨2876333925594378590416331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917555950396252393610887 2876333925594378590416331)
                ·
                  refine ⟨4314500888391567885624497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876333925594378590416331 4314500888391567885624497)
                  ·
                    refine ⟨3235875666293675914218373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314500888391567885624497 3235875666293675914218373)
                    ·
                      refine ⟨606726687430064233915945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3235875666293675914218373 606726687430064233915945)
                      ·
                        rfl

theorem cell23_1181596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1181596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181596 prefixEnd_1181596 := by exact prefixLift 1181596
  have htrace : WordTrace (prefixWord ++ tailWord_1181596) baseStart_1181596 baseEnd_1181596 := by
    simpa [prefixWord, tailWord_1181596, baseEnd_1181596] using wordTrace_append hprefix tailTrace_1181596
  have hstable : (prefixWord ++ tailWord_1181596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181596).length < 2 ^ (prefixWord ++ tailWord_1181596).sum := by decide
  have hdescent : baseEnd_1181596 < baseStart_1181596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181617 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1181617 : Nat := 118140960795 + 1181617 * 2 ^ 59
def prefixEnd_1181617 : Nat := 4983230072969 + 3 ^ 40 * 1181617 * 2
def baseEnd_1181617 : Nat := 606737470523808651753349

theorem tailTrace_1181617 : CollatzResearch.WordTrace tailWord_1181617 prefixEnd_1181617 606737470523808651753349 := by
  unfold tailWord_1181617
  simp only [CollatzResearch.WordTrace]
  refine ⟨43097112560210887962263105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28731408373473925308175403 43097112560210887962263105)
  ·
    refine ⟨32322834420158165971697329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43097112560210887962263105 32322834420158165971697329)
    ·
      refine ⟨24242125815118624478772997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32322834420158165971697329 24242125815118624478772997)
      ·
        refine ⟨4545398590334742089769937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24242125815118624478772997 4545398590334742089769937)
        ·
          refine ⟨3409048942751056567327453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4545398590334742089769937 3409048942751056567327453)
          ·
            refine ⟨1278393353531646212747795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3409048942751056567327453 1278393353531646212747795)
            ·
              refine ⟨1917590030297469319121693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278393353531646212747795 1917590030297469319121693)
              ·
                refine ⟨719096261361550994670635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1917590030297469319121693 719096261361550994670635)
                ·
                  refine ⟨1078644392042326492005953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719096261361550994670635 1078644392042326492005953)
                  ·
                    refine ⟨808983294031744869004465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1078644392042326492005953 808983294031744869004465)
                    ·
                      refine ⟨606737470523808651753349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 808983294031744869004465 606737470523808651753349)
                      ·
                        rfl

theorem cell23_1181617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1181617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181617 prefixEnd_1181617 := by exact prefixLift 1181617
  have htrace : WordTrace (prefixWord ++ tailWord_1181617) baseStart_1181617 baseEnd_1181617 := by
    simpa [prefixWord, tailWord_1181617, baseEnd_1181617] using wordTrace_append hprefix tailTrace_1181617
  have hstable : (prefixWord ++ tailWord_1181617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181617).length < 2 ^ (prefixWord ++ tailWord_1181617).sum := by decide
  have hdescent : baseEnd_1181617 < baseStart_1181617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181650 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1181650 : Nat := 118140960795 + 1181650 * 2 ^ 59
def prefixEnd_1181650 : Nat := 4983230072969 + 3 ^ 40 * 1181650 * 2
def baseEnd_1181650 : Nat := 606754415385407022640697

theorem tailTrace_1181650 : CollatzResearch.WordTrace tailWord_1181650 prefixEnd_1181650 606754415385407022640697 := by
  unfold tailWord_1181650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774579042272833649553601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28732210779394223065476269 10774579042272833649553601)
  ·
    refine ⟨8080934281704625237165201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10774579042272833649553601 8080934281704625237165201)
    ·
      refine ⟨6060700711278468927873901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8080934281704625237165201 6060700711278468927873901)
      ·
        refine ⟨2272762766729425847952713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6060700711278468927873901 2272762766729425847952713)
        ·
          refine ⟨1704572075047069385964535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272762766729425847952713 1704572075047069385964535)
          ·
            refine ⟨2556858112570604078946803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704572075047069385964535 2556858112570604078946803)
            ·
              refine ⟨3835287168855906118420205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556858112570604078946803 3835287168855906118420205)
              ·
                refine ⟨1438232688320964794407577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3835287168855906118420205 1438232688320964794407577)
                ·
                  refine ⟨1078674516240723595805683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1438232688320964794407577 1078674516240723595805683)
                  ·
                    refine ⟨1618011774361085393708525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1078674516240723595805683 1618011774361085393708525)
                    ·
                      refine ⟨606754415385407022640697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1618011774361085393708525 606754415385407022640697)
                      ·
                        rfl

theorem cell23_1181650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1181650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181650 prefixEnd_1181650 := by exact prefixLift 1181650
  have htrace : WordTrace (prefixWord ++ tailWord_1181650) baseStart_1181650 baseEnd_1181650 := by
    simpa [prefixWord, tailWord_1181650, baseEnd_1181650] using wordTrace_append hprefix tailTrace_1181650
  have hstable : (prefixWord ++ tailWord_1181650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181650).length < 2 ^ (prefixWord ++ tailWord_1181650).sum := by decide
  have hdescent : baseEnd_1181650 < baseStart_1181650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181656 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1181656 : Nat := 118140960795 + 1181656 * 2 ^ 59
def prefixEnd_1181656 : Nat := 4983230072969 + 3 ^ 40 * 1181656 * 2
def baseEnd_1181656 : Nat := 606757496269333999165669

theorem tailTrace_1181656 : CollatzResearch.WordTrace tailWord_1181656 prefixEnd_1181656 606757496269333999165669 := by
  unfold tailWord_1181656
  simp only [CollatzResearch.WordTrace]
  refine ⟨21549267503534798811466411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28732356671379731748621881 21549267503534798811466411)
  ·
    refine ⟨32323901255302198217199617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21549267503534798811466411 32323901255302198217199617)
    ·
      refine ⟨24242925941476648662899713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32323901255302198217199617 24242925941476648662899713)
      ·
        refine ⟨18182194456107486497174785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24242925941476648662899713 18182194456107486497174785)
        ·
          refine ⟨13636645842080614872881089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18182194456107486497174785 13636645842080614872881089)
          ·
            refine ⟨10227484381560461154660817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13636645842080614872881089 10227484381560461154660817)
            ·
              refine ⟨7670613286170345865995613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10227484381560461154660817 7670613286170345865995613)
              ·
                refine ⟨2876479982313879699748355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7670613286170345865995613 2876479982313879699748355)
                ·
                  refine ⟨4314719973470819549622533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876479982313879699748355 4314719973470819549622533)
                  ·
                    refine ⟨809009995025778665554225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314719973470819549622533 809009995025778665554225)
                    ·
                      refine ⟨606757496269333999165669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809009995025778665554225 606757496269333999165669)
                      ·
                        rfl

theorem cell23_1181656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1181656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181656 prefixEnd_1181656 := by exact prefixLift 1181656
  have htrace : WordTrace (prefixWord ++ tailWord_1181656) baseStart_1181656 baseEnd_1181656 := by
    simpa [prefixWord, tailWord_1181656, baseEnd_1181656] using wordTrace_append hprefix tailTrace_1181656
  have hstable : (prefixWord ++ tailWord_1181656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181656).length < 2 ^ (prefixWord ++ tailWord_1181656).sum := by decide
  have hdescent : baseEnd_1181656 < baseStart_1181656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181749 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1181749 : Nat := 118140960795 + 1181749 * 2 ^ 59
def prefixEnd_1181749 : Nat := 4983230072969 + 3 ^ 40 * 1181749 * 2
def baseEnd_1181749 : Nat := 606805249970202135302741

theorem tailTrace_1181749 : CollatzResearch.WordTrace tailWord_1181749 prefixEnd_1181749 606805249970202135302741 := by
  unfold tailWord_1181749
  simp only [CollatzResearch.WordTrace]
  refine ⟨43101926995732674506068301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28734617997155116337378867 43101926995732674506068301)
  ·
    refine ⟨16163222623399752939775613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43101926995732674506068301 16163222623399752939775613)
    ·
      refine ⟨6061208483774907352415855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16163222623399752939775613 6061208483774907352415855)
      ·
        refine ⟨9091812725662361028623783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6061208483774907352415855 9091812725662361028623783)
        ·
          refine ⟨13637719088493541542935675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9091812725662361028623783 13637719088493541542935675)
          ·
            refine ⟨20456578632740312314403513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13637719088493541542935675 20456578632740312314403513)
            ·
              refine ⟨15342433974555234235802635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20456578632740312314403513 15342433974555234235802635)
              ·
                refine ⟨23013650961832851353703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15342433974555234235802635 23013650961832851353703953)
                ·
                  refine ⟨17260238221374638515277965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23013650961832851353703953 17260238221374638515277965)
                  ·
                    refine ⟨6472589333015489443229237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17260238221374638515277965 6472589333015489443229237)
                    ·
                      refine ⟨606805249970202135302741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6472589333015489443229237 606805249970202135302741)
                      ·
                        rfl

theorem cell23_1181749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1181749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181749 prefixEnd_1181749 := by exact prefixLift 1181749
  have htrace : WordTrace (prefixWord ++ tailWord_1181749) baseStart_1181749 baseEnd_1181749 := by
    simpa [prefixWord, tailWord_1181749, baseEnd_1181749] using wordTrace_append hprefix tailTrace_1181749
  have hstable : (prefixWord ++ tailWord_1181749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181749).length < 2 ^ (prefixWord ++ tailWord_1181749).sum := by decide
  have hdescent : baseEnd_1181749 < baseStart_1181749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181773 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1181773 : Nat := 118140960795 + 1181773 * 2 ^ 59
def prefixEnd_1181773 : Nat := 4983230072969 + 3 ^ 40 * 1181773 * 2
def baseEnd_1181773 : Nat := 202272524501970013800877

theorem tailTrace_1181773 : CollatzResearch.WordTrace tailWord_1181773 prefixEnd_1181773 202272524501970013800877 := by
  unfold tailWord_1181773
  simp only [CollatzResearch.WordTrace]
  refine ⟨43102802347645726604941973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28735201565097151069961315 43102802347645726604941973)
  ·
    refine ⟨2020443860045893434606655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43102802347645726604941973 2020443860045893434606655)
    ·
      refine ⟨3030665790068840151909983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020443860045893434606655 3030665790068840151909983)
      ·
        refine ⟨4545998685103260227864975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030665790068840151909983 4545998685103260227864975)
        ·
          refine ⟨6818998027654890341797463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545998685103260227864975 6818998027654890341797463)
          ·
            refine ⟨10228497041482335512696195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818998027654890341797463 10228497041482335512696195)
            ·
              refine ⟨15342745562223503269044293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10228497041482335512696195 15342745562223503269044293)
              ·
                refine ⟨2876764792916906862945805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15342745562223503269044293 2876764792916906862945805)
                ·
                  refine ⟨1078786797343840073604677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2876764792916906862945805 1078786797343840073604677)
                  ·
                    refine ⟨202272524501970013800877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1078786797343840073604677 202272524501970013800877)
                    ·
                      rfl

theorem cell23_1181773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1181773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181773 prefixEnd_1181773 := by exact prefixLift 1181773
  have htrace : WordTrace (prefixWord ++ tailWord_1181773) baseStart_1181773 baseEnd_1181773 := by
    simpa [prefixWord, tailWord_1181773, baseEnd_1181773] using wordTrace_append hprefix tailTrace_1181773
  have hstable : (prefixWord ++ tailWord_1181773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181773).length < 2 ^ (prefixWord ++ tailWord_1181773).sum := by decide
  have hdescent : baseEnd_1181773 < baseStart_1181773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181819 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_1181819 : Nat := 118140960795 + 1181819 * 2 ^ 59
def prefixEnd_1181819 : Nat := 4983230072969 + 3 ^ 40 * 1181819 * 2
def baseEnd_1181819 : Nat := 606841193616016861427419

theorem tailTrace_1181819 : CollatzResearch.WordTrace tailWord_1181819 prefixEnd_1181819 606841193616016861427419 := by
  unfold tailWord_1181819
  simp only [CollatzResearch.WordTrace]
  refine ⟨43104480105479076461116511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28736320070319384307411007 43104480105479076461116511)
  ·
    refine ⟨64656720158218614691674767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43104480105479076461116511 64656720158218614691674767)
    ·
      refine ⟨96985080237327922037512151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64656720158218614691674767 96985080237327922037512151)
      ·
        refine ⟨145477620355991883056268227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96985080237327922037512151 145477620355991883056268227)
        ·
          refine ⟨218216430533987824584402341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145477620355991883056268227 218216430533987824584402341)
          ·
            refine ⟨40915580725122717109575439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218216430533987824584402341 40915580725122717109575439)
            ·
              refine ⟨61373371087684075664363159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40915580725122717109575439 61373371087684075664363159)
              ·
                refine ⟨92060056631526113496544739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61373371087684075664363159 92060056631526113496544739)
                ·
                  refine ⟨138090084947289170244817109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92060056631526113496544739 138090084947289170244817109)
                  ·
                    refine ⟨3236486365952089927612901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138090084947289170244817109 3236486365952089927612901)
                    ·
                      refine ⟨606841193616016861427419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3236486365952089927612901 606841193616016861427419)
                      ·
                        rfl

theorem cell23_1181819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_1181819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181819 prefixEnd_1181819 := by exact prefixLift 1181819
  have htrace : WordTrace (prefixWord ++ tailWord_1181819) baseStart_1181819 baseEnd_1181819 := by
    simpa [prefixWord, tailWord_1181819, baseEnd_1181819] using wordTrace_append hprefix tailTrace_1181819
  have hstable : (prefixWord ++ tailWord_1181819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181819).length < 2 ^ (prefixWord ++ tailWord_1181819).sum := by decide
  have hdescent : baseEnd_1181819 < baseStart_1181819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181903 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_1181903 : Nat := 118140960795 + 1181903 * 2 ^ 59
def prefixEnd_1181903 : Nat := 4983230072969 + 3 ^ 40 * 1181903 * 2
def baseEnd_1181903 : Nat := 606884325990994532777033

theorem tailTrace_1181903 : CollatzResearch.WordTrace tailWord_1181903 prefixEnd_1181903 606884325990994532777033 := by
  unfold tailWord_1181903
  simp only [CollatzResearch.WordTrace]
  refine ⟨43107543837174758807174363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28738362558116505871449575 43107543837174758807174363)
  ·
    refine ⟨64661315755762138210761545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43107543837174758807174363 64661315755762138210761545)
    ·
      refine ⟨48495986816821603658071159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64661315755762138210761545 48495986816821603658071159)
      ·
        refine ⟨72743980225232405487106739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48495986816821603658071159 72743980225232405487106739)
        ·
          refine ⟨109115970337848608230660109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72743980225232405487106739 109115970337848608230660109)
          ·
            refine ⟨40918488876693228086497541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109115970337848608230660109 40918488876693228086497541)
            ·
              refine ⟨7672216664379980266218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40918488876693228086497541 7672216664379980266218289)
              ·
                refine ⟨5754162498284985199663717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7672216664379980266218289 5754162498284985199663717)
                ·
                  refine ⟨1078905468428434724936947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5754162498284985199663717 1078905468428434724936947)
                  ·
                    refine ⟨1618358202642652087405421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1078905468428434724936947 1618358202642652087405421)
                    ·
                      refine ⟨606884325990994532777033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1618358202642652087405421 606884325990994532777033)
                      ·
                        rfl

theorem cell23_1181903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_1181903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181903 prefixEnd_1181903 := by exact prefixLift 1181903
  have htrace : WordTrace (prefixWord ++ tailWord_1181903) baseStart_1181903 baseEnd_1181903 := by
    simpa [prefixWord, tailWord_1181903, baseEnd_1181903] using wordTrace_append hprefix tailTrace_1181903
  have hstable : (prefixWord ++ tailWord_1181903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181903).length < 2 ^ (prefixWord ++ tailWord_1181903).sum := by decide
  have hdescent : baseEnd_1181903 < baseStart_1181903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181976 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1181976 : Nat := 118140960795 + 1181976 * 2 ^ 59
def prefixEnd_1181976 : Nat := 4983230072969 + 3 ^ 40 * 1181976 * 2
def baseEnd_1181976 : Nat := 606921810078772747164197

theorem tailTrace_1181976 : CollatzResearch.WordTrace tailWord_1181976 prefixEnd_1181976 606921810078772747164197 := by
  unfold tailWord_1181976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555103182955146137290891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28740137577273528183054521 21555103182955146137290891)
  ·
    refine ⟨32332654774432719205936337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21555103182955146137290891 32332654774432719205936337)
    ·
      refine ⟨24249491080824539404452253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32332654774432719205936337 24249491080824539404452253)
      ·
        refine ⟨9093559155309202276669595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24249491080824539404452253 9093559155309202276669595)
        ·
          refine ⟨13640338732963803415004393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093559155309202276669595 13640338732963803415004393)
          ·
            refine ⟨10230254049722852561253295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13640338732963803415004393 10230254049722852561253295)
            ·
              refine ⟨15345381074584278841879943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10230254049722852561253295 15345381074584278841879943)
              ·
                refine ⟨23018071611876418262819915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15345381074584278841879943 23018071611876418262819915)
                ·
                  refine ⟨34527107417814627394229873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23018071611876418262819915 34527107417814627394229873)
                  ·
                    refine ⟨25895330563360970545672405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34527107417814627394229873 25895330563360970545672405)
                    ·
                      refine ⟨606921810078772747164197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25895330563360970545672405 606921810078772747164197)
                      ·
                        rfl

theorem cell23_1181976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1181976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181976 prefixEnd_1181976 := by exact prefixLift 1181976
  have htrace : WordTrace (prefixWord ++ tailWord_1181976) baseStart_1181976 baseEnd_1181976 := by
    simpa [prefixWord, tailWord_1181976, baseEnd_1181976] using wordTrace_append hprefix tailTrace_1181976
  have hstable : (prefixWord ++ tailWord_1181976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181976).length < 2 ^ (prefixWord ++ tailWord_1181976).sum := by decide
  have hdescent : baseEnd_1181976 < baseStart_1181976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181983 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 7]
def baseStart_1181983 : Nat := 118140960795 + 1181983 * 2 ^ 59
def prefixEnd_1181983 : Nat := 4983230072969 + 3 ^ 40 * 1181983 * 2
def baseEnd_1181983 : Nat := 67436156049261579975185

theorem tailTrace_1181983 : CollatzResearch.WordTrace tailWord_1181983 prefixEnd_1181983 67436156049261579975185 := by
  unfold tailWord_1181983
  simp only [CollatzResearch.WordTrace]
  refine ⟨43110461676884932470086603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28740307784589954980057735 43110461676884932470086603)
  ·
    refine ⟨64665692515327398705129905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43110461676884932470086603 64665692515327398705129905)
    ·
      refine ⟨48499269386495549028847429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64665692515327398705129905 48499269386495549028847429)
      ·
        refine ⟨9093613009967915442908893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48499269386495549028847429 9093613009967915442908893)
        ·
          refine ⟨3410104878737968291090835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9093613009967915442908893 3410104878737968291090835)
          ·
            refine ⟨5115157318106952436636253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410104878737968291090835 5115157318106952436636253)
            ·
              refine ⟨1918183994290107163738595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5115157318106952436636253 1918183994290107163738595)
              ·
                refine ⟨2877275991435160745607893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918183994290107163738595 2877275991435160745607893)
                ·
                  refine ⟨67436156049261579975185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2877275991435160745607893 67436156049261579975185)
                  ·
                    rfl

theorem cell23_1181983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 7].length) (baseStart_1181983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181983 prefixEnd_1181983 := by exact prefixLift 1181983
  have htrace : WordTrace (prefixWord ++ tailWord_1181983) baseStart_1181983 baseEnd_1181983 := by
    simpa [prefixWord, tailWord_1181983, baseEnd_1181983] using wordTrace_append hprefix tailTrace_1181983
  have hstable : (prefixWord ++ tailWord_1181983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181983).length < 2 ^ (prefixWord ++ tailWord_1181983).sum := by decide
  have hdescent : baseEnd_1181983 < baseStart_1181983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181996 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_1181996 : Nat := 118140960795 + 1181996 * 2 ^ 59
def prefixEnd_1181996 : Nat := 4983230072969 + 3 ^ 40 * 1181996 * 2
def baseEnd_1181996 : Nat := 202310693230620889638035

theorem tailTrace_1181996 : CollatzResearch.WordTrace tailWord_1181996 prefixEnd_1181996 202310693230620889638035 := by
  unfold tailWord_1181996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555467912918917845154921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28740623883891890460206561 21555467912918917845154921)
  ·
    refine ⟨16166600934689188383866191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21555467912918917845154921 16166600934689188383866191)
    ·
      refine ⟨24249901402033782575799287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16166600934689188383866191 24249901402033782575799287)
      ·
        refine ⟨36374852103050673863698931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24249901402033782575799287 36374852103050673863698931)
        ·
          refine ⟨54562278154576010795548397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36374852103050673863698931 54562278154576010795548397)
          ·
            refine ⟨20460854307966004048330649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54562278154576010795548397 20460854307966004048330649)
            ·
              refine ⟨15345640730974503036247987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20460854307966004048330649 15345640730974503036247987)
              ·
                refine ⟨23018461096461754554371981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15345640730974503036247987 23018461096461754554371981)
                ·
                  refine ⟨8631922911173157957889493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23018461096461754554371981 8631922911173157957889493)
                  ·
                    refine ⟨202310693230620889638035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8631922911173157957889493 202310693230620889638035)
                    ·
                      rfl

theorem cell23_1181996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_1181996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181996 prefixEnd_1181996 := by exact prefixLift 1181996
  have htrace : WordTrace (prefixWord ++ tailWord_1181996) baseStart_1181996 baseEnd_1181996 := by
    simpa [prefixWord, tailWord_1181996, baseEnd_1181996] using wordTrace_append hprefix tailTrace_1181996
  have hstable : (prefixWord ++ tailWord_1181996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181996).length < 2 ^ (prefixWord ++ tailWord_1181996).sum := by decide
  have hdescent : baseEnd_1181996 < baseStart_1181996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181998 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1181998 : Nat := 118140960795 + 1181998 * 2 ^ 59
def prefixEnd_1181998 : Nat := 4983230072969 + 3 ^ 40 * 1181998 * 2
def baseEnd_1181998 : Nat := 606933106653171661089097

theorem tailTrace_1181998 : CollatzResearch.WordTrace tailWord_1181998 prefixEnd_1181998 606933106653171661089097 := by
  unfold tailWord_1181998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388876096478823753985331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28740672514553726687921765 5388876096478823753985331)
  ·
    refine ⟨8083314144718235630977997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5388876096478823753985331 8083314144718235630977997)
    ·
      refine ⟨3031242804269338361616749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8083314144718235630977997 3031242804269338361616749)
      ·
        refine ⟨1136716051601001885606281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3031242804269338361616749 1136716051601001885606281)
        ·
          refine ⟨852537038700751414204711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136716051601001885606281 852537038700751414204711)
          ·
            refine ⟨1278805558051127121307067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852537038700751414204711 1278805558051127121307067)
            ·
              refine ⟨1918208337076690681960601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278805558051127121307067 1918208337076690681960601)
              ·
                refine ⟨1438656252807518011470451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918208337076690681960601 1438656252807518011470451)
                ·
                  refine ⟨2157984379211277017205677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438656252807518011470451 2157984379211277017205677)
                  ·
                    refine ⟨809244142204228881452129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157984379211277017205677 809244142204228881452129)
                    ·
                      refine ⟨606933106653171661089097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809244142204228881452129 606933106653171661089097)
                      ·
                        rfl

theorem cell23_1181998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1181998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1181998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1181998 prefixEnd_1181998 := by exact prefixLift 1181998
  have htrace : WordTrace (prefixWord ++ tailWord_1181998) baseStart_1181998 baseEnd_1181998 := by
    simpa [prefixWord, tailWord_1181998, baseEnd_1181998] using wordTrace_append hprefix tailTrace_1181998
  have hstable : (prefixWord ++ tailWord_1181998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181998).length < 2 ^ (prefixWord ++ tailWord_1181998).sum := by decide
  have hdescent : baseEnd_1181998 < baseStart_1181998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182077 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1182077 : Nat := 118140960795 + 1182077 * 2 ^ 59
def prefixEnd_1182077 : Nat := 4983230072969 + 3 ^ 40 * 1182077 * 2
def baseEnd_1182077 : Nat := 202324557208292284000411

theorem tailTrace_1182077 : CollatzResearch.WordTrace tailWord_1182077 prefixEnd_1182077 202324557208292284000411 := by
  unfold tailWord_1182077
  simp only [CollatzResearch.WordTrace]
  refine ⟨43113890138544386524008485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28742593425696257682672323 43113890138544386524008485)
  ·
    refine ⟨8083854400977072473251591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43113890138544386524008485 8083854400977072473251591)
    ·
      refine ⟨12125781601465608709877387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8083854400977072473251591 12125781601465608709877387)
      ·
        refine ⟨18188672402198413064816081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125781601465608709877387 18188672402198413064816081)
        ·
          refine ⟨13641504301648809798612061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18188672402198413064816081 13641504301648809798612061)
          ·
            refine ⟨5115564113118303674479523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13641504301648809798612061 5115564113118303674479523)
            ·
              refine ⟨7673346169677455511719285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115564113118303674479523 7673346169677455511719285)
              ·
                refine ⟨719376203407261454223683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7673346169677455511719285 719376203407261454223683)
                ·
                  refine ⟨1079064305110892181335525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719376203407261454223683 1079064305110892181335525)
                  ·
                    refine ⟨202324557208292284000411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079064305110892181335525 202324557208292284000411)
                    ·
                      rfl

theorem cell23_1182077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1182077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182077 prefixEnd_1182077 := by exact prefixLift 1182077
  have htrace : WordTrace (prefixWord ++ tailWord_1182077) baseStart_1182077 baseEnd_1182077 := by
    simpa [prefixWord, tailWord_1182077, baseEnd_1182077] using wordTrace_append hprefix tailTrace_1182077
  have hstable : (prefixWord ++ tailWord_1182077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182077).length < 2 ^ (prefixWord ++ tailWord_1182077).sum := by decide
  have hdescent : baseEnd_1182077 < baseStart_1182077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182094 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1182094 : Nat := 118140960795 + 1182094 * 2 ^ 59
def prefixEnd_1182094 : Nat := 4983230072969 + 3 ^ 40 * 1182094 * 2
def baseEnd_1182094 : Nat := 202327466932001095162885

theorem tailTrace_1182094 : CollatzResearch.WordTrace tailWord_1182094 prefixEnd_1182094 202327466932001095162885 := by
  unfold tailWord_1182094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389313772435349803422167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28743006786321865618251557 5389313772435349803422167)
  ·
    refine ⟨8083970658653024705133251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5389313772435349803422167 8083970658653024705133251)
    ·
      refine ⟨12125955987979537057699877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8083970658653024705133251 12125955987979537057699877)
      ·
        refine ⟨2273616747746163198318727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12125955987979537057699877 2273616747746163198318727)
        ·
          refine ⟨3410425121619244797478091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273616747746163198318727 3410425121619244797478091)
          ·
            refine ⟨5115637682428867196217137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410425121619244797478091 5115637682428867196217137)
            ·
              refine ⟨3836728261821650397162853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5115637682428867196217137 3836728261821650397162853)
              ·
                refine ⟨719386549091559449468035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3836728261821650397162853 719386549091559449468035)
                ·
                  refine ⟨1079079823637339174202053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719386549091559449468035 1079079823637339174202053)
                  ·
                    refine ⟨202327466932001095162885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079079823637339174202053 202327466932001095162885)
                    ·
                      rfl

theorem cell23_1182094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1182094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182094 prefixEnd_1182094 := by exact prefixLift 1182094
  have htrace : WordTrace (prefixWord ++ tailWord_1182094) baseStart_1182094 baseEnd_1182094 := by
    simpa [prefixWord, tailWord_1182094, baseEnd_1182094] using wordTrace_append hprefix tailTrace_1182094
  have hstable : (prefixWord ++ tailWord_1182094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182094).length < 2 ^ (prefixWord ++ tailWord_1182094).sum := by decide
  have hdescent : baseEnd_1182094 < baseStart_1182094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182103 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 5, 5]
def baseStart_1182103 : Nat := 118140960795 + 1182103 * 2 ^ 59
def prefixEnd_1182103 : Nat := 4983230072969 + 3 ^ 40 * 1182103 * 2
def baseEnd_1182103 : Nat := 202329007373964583425371

theorem tailTrace_1182103 : CollatzResearch.WordTrace tailWord_1182103 prefixEnd_1182103 202329007373964583425371 := by
  unfold tailWord_1182103
  simp only [CollatzResearch.WordTrace]
  refine ⟨43114838436450192964454963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28743225624300128642969975 43114838436450192964454963)
  ·
    refine ⟨64672257654675289446682445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43114838436450192964454963 64672257654675289446682445)
    ·
      refine ⟨24252096620503233542505917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64672257654675289446682445 24252096620503233542505917)
      ·
        refine ⟨9094536232688712578439719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24252096620503233542505917 9094536232688712578439719)
        ·
          refine ⟨13641804349033068867659579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9094536232688712578439719 13641804349033068867659579)
          ·
            refine ⟨20462706523549603301489369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13641804349033068867659579 20462706523549603301489369)
            ·
              refine ⟨15347029892662202476117027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20462706523549603301489369 15347029892662202476117027)
              ·
                refine ⟨23020544838993303714175541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15347029892662202476117027 23020544838993303714175541)
                ·
                  refine ⟨2158176078655622223203957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23020544838993303714175541 2158176078655622223203957)
                  ·
                    refine ⟨202329007373964583425371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2158176078655622223203957 202329007373964583425371)
                    ·
                      rfl

theorem cell23_1182103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_1182103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182103 prefixEnd_1182103 := by exact prefixLift 1182103
  have htrace : WordTrace (prefixWord ++ tailWord_1182103) baseStart_1182103 baseEnd_1182103 := by
    simpa [prefixWord, tailWord_1182103, baseEnd_1182103] using wordTrace_append hprefix tailTrace_1182103
  have hstable : (prefixWord ++ tailWord_1182103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182103).length < 2 ^ (prefixWord ++ tailWord_1182103).sum := by decide
  have hdescent : baseEnd_1182103 < baseStart_1182103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182145 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1182145 : Nat := 118140960795 + 1182145 * 2 ^ 59
def prefixEnd_1182145 : Nat := 4983230072969 + 3 ^ 40 * 1182145 * 2
def baseEnd_1182145 : Nat := 202336196103127528650307

theorem tailTrace_1182145 : CollatzResearch.WordTrace tailWord_1182145 prefixEnd_1182145 202336196103127528650307 := by
  unfold tailWord_1182145
  simp only [CollatzResearch.WordTrace]
  refine ⟨43116370302298034137483889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28744246868198689424989259 43116370302298034137483889)
  ·
    refine ⟨32337277726723525603112917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43116370302298034137483889 32337277726723525603112917)
    ·
      refine ⟨757904946720082631322959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32337277726723525603112917 757904946720082631322959)
      ·
        refine ⟨1136857420080123946984439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757904946720082631322959 1136857420080123946984439)
        ·
          refine ⟨1705286130120185920476659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136857420080123946984439 1705286130120185920476659)
          ·
            refine ⟨2557929195180278880714989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705286130120185920476659 2557929195180278880714989)
            ·
              refine ⟨959223448192604580268121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2557929195180278880714989 959223448192604580268121)
              ·
                refine ⟨719417586144453435201091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959223448192604580268121 719417586144453435201091)
                ·
                  refine ⟨1079126379216680152801637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719417586144453435201091 1079126379216680152801637)
                  ·
                    refine ⟨202336196103127528650307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079126379216680152801637 202336196103127528650307)
                    ·
                      rfl

theorem cell23_1182145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1182145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182145 prefixEnd_1182145 := by exact prefixLift 1182145
  have htrace : WordTrace (prefixWord ++ tailWord_1182145) baseStart_1182145 baseEnd_1182145 := by
    simpa [prefixWord, tailWord_1182145, baseEnd_1182145] using wordTrace_append hprefix tailTrace_1182145
  have hstable : (prefixWord ++ tailWord_1182145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182145).length < 2 ^ (prefixWord ++ tailWord_1182145).sum := by decide
  have hdescent : baseEnd_1182145 < baseStart_1182145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182151 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_1182151 : Nat := 118140960795 + 1182151 * 2 ^ 59
def prefixEnd_1182151 : Nat := 4983230072969 + 3 ^ 40 * 1182151 * 2
def baseEnd_1182151 : Nat := 607011669193309562475893

theorem tailTrace_1182151 : CollatzResearch.WordTrace tailWord_1182151 prefixEnd_1182151 607011669193309562475893 := by
  unfold tailWord_1182151
  simp only [CollatzResearch.WordTrace]
  refine ⟨43116589140276297162202307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28744392760184198108134871 43116589140276297162202307)
  ·
    refine ⟨64674883710414445743303461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43116589140276297162202307 64674883710414445743303461)
    ·
      refine ⟨12126540695702708576869399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64674883710414445743303461 12126540695702708576869399)
      ·
        refine ⟨18189811043554062865304099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12126540695702708576869399 18189811043554062865304099)
        ·
          refine ⟨27284716565331094297956149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18189811043554062865304099 27284716565331094297956149)
          ·
            refine ⟨2557942177999790090433389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27284716565331094297956149 2557942177999790090433389)
            ·
              refine ⟨959228316749921283912521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2557942177999790090433389 959228316749921283912521)
              ·
                refine ⟨719421237562440962934391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959228316749921283912521 719421237562440962934391)
                ·
                  refine ⟨1079131856343661444401587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719421237562440962934391 1079131856343661444401587)
                  ·
                    refine ⟨1618697784515492166602381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079131856343661444401587 1618697784515492166602381)
                    ·
                      refine ⟨607011669193309562475893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1618697784515492166602381 607011669193309562475893)
                      ·
                        rfl

theorem cell23_1182151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_1182151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182151 prefixEnd_1182151 := by exact prefixLift 1182151
  have htrace : WordTrace (prefixWord ++ tailWord_1182151) baseStart_1182151 baseEnd_1182151 := by
    simpa [prefixWord, tailWord_1182151, baseEnd_1182151] using wordTrace_append hprefix tailTrace_1182151
  have hstable : (prefixWord ++ tailWord_1182151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182151).length < 2 ^ (prefixWord ++ tailWord_1182151).sum := by decide
  have hdescent : baseEnd_1182151 < baseStart_1182151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182153 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_1182153 : Nat := 118140960795 + 1182153 * 2 ^ 59
def prefixEnd_1182153 : Nat := 4983230072969 + 3 ^ 40 * 1182153 * 2
def baseEnd_1182153 : Nat := 607012696154618554650883

theorem tailTrace_1182153 : CollatzResearch.WordTrace tailWord_1182153 prefixEnd_1182153 607012696154618554650883 := by
  unfold tailWord_1182153
  simp only [CollatzResearch.WordTrace]
  refine ⟨43116662086269051503775113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28744441390846034335850075 43116662086269051503775113)
  ·
    refine ⟨32337496564701788627831335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43116662086269051503775113 32337496564701788627831335)
    ·
      refine ⟨48506244847052682941747003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32337496564701788627831335 48506244847052682941747003)
      ·
        refine ⟨72759367270579024412620505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48506244847052682941747003 72759367270579024412620505)
        ·
          refine ⟨54569525452934268309465379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72759367270579024412620505 54569525452934268309465379)
          ·
            refine ⟨81854288179401402464198069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54569525452934268309465379 81854288179401402464198069)
            ·
              refine ⟨7673839516818881481018569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81854288179401402464198069 7673839516818881481018569)
              ·
                refine ⟨5755379637614161110763927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7673839516818881481018569 5755379637614161110763927)
                ·
                  refine ⟨8633069456421241666145891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755379637614161110763927 8633069456421241666145891)
                  ·
                    refine ⟨12949604184631862499218837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8633069456421241666145891 12949604184631862499218837)
                    ·
                      refine ⟨607012696154618554650883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12949604184631862499218837 607012696154618554650883)
                      ·
                        rfl

theorem cell23_1182153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_1182153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182153 prefixEnd_1182153 := by exact prefixLift 1182153
  have htrace : WordTrace (prefixWord ++ tailWord_1182153) baseStart_1182153 baseEnd_1182153 := by
    simpa [prefixWord, tailWord_1182153, baseEnd_1182153] using wordTrace_append hprefix tailTrace_1182153
  have hstable : (prefixWord ++ tailWord_1182153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182153).length < 2 ^ (prefixWord ++ tailWord_1182153).sum := by decide
  have hdescent : baseEnd_1182153 < baseStart_1182153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182170 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1182170 : Nat := 118140960795 + 1182170 * 2 ^ 59
def prefixEnd_1182170 : Nat := 4983230072969 + 3 ^ 40 * 1182170 * 2
def baseEnd_1182170 : Nat := 607021425325744988138305

theorem tailTrace_1182170 : CollatzResearch.WordTrace tailWord_1182170 prefixEnd_1182170 607021425325744988138305 := by
  unfold tailWord_1182170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10779320531801865851785991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28744854751471642271429309 10779320531801865851785991)
  ·
    refine ⟨16168980797702798777678987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10779320531801865851785991 16168980797702798777678987)
    ·
      refine ⟨24253471196554198166518481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16168980797702798777678987 24253471196554198166518481)
      ·
        refine ⟨18190103397415648624888861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24253471196554198166518481 18190103397415648624888861)
        ·
          refine ⟨6821288774030868234333323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18190103397415648624888861 6821288774030868234333323)
          ·
            refine ⟨10231933161046302351499985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821288774030868234333323 10231933161046302351499985)
            ·
              refine ⟨7673949870784726763624989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10231933161046302351499985 7673949870784726763624989)
              ·
                refine ⟨2877731201544272536359371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7673949870784726763624989 2877731201544272536359371)
                ·
                  refine ⟨4316596802316408804539057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877731201544272536359371 4316596802316408804539057)
                  ·
                    refine ⟨3237447601737306603404293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316596802316408804539057 3237447601737306603404293)
                    ·
                      refine ⟨607021425325744988138305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3237447601737306603404293 607021425325744988138305)
                      ·
                        rfl

theorem cell23_1182170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1182170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182170 prefixEnd_1182170 := by exact prefixLift 1182170
  have htrace : WordTrace (prefixWord ++ tailWord_1182170) baseStart_1182170 baseEnd_1182170 := by
    simpa [prefixWord, tailWord_1182170, baseEnd_1182170] using wordTrace_append hprefix tailTrace_1182170
  have hstable : (prefixWord ++ tailWord_1182170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182170).length < 2 ^ (prefixWord ++ tailWord_1182170).sum := by decide
  have hdescent : baseEnd_1182170 < baseStart_1182170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182178 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1182178 : Nat := 118140960795 + 1182178 * 2 ^ 59
def prefixEnd_1182178 : Nat := 4983230072969 + 3 ^ 40 * 1182178 * 2
def baseEnd_1182178 : Nat := 607025533170980956838269

theorem tailTrace_1182178 : CollatzResearch.WordTrace tailWord_1182178 prefixEnd_1182178 607025533170980956838269 := by
  unfold tailWord_1182178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10779393477794620193358797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28745049274118987182290125 10779393477794620193358797)
  ·
    refine ⟨4042272554172982572509549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10779393477794620193358797 4042272554172982572509549)
    ·
      refine ⟨1515852207814868464691081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4042272554172982572509549 1515852207814868464691081)
      ·
        refine ⟨1136889155861151348518311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1515852207814868464691081 1136889155861151348518311)
        ·
          refine ⟨1705333733791727022777467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136889155861151348518311 1705333733791727022777467)
          ·
            refine ⟨2558000600687590534166201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705333733791727022777467 2558000600687590534166201)
            ·
              refine ⟨1918500450515692900624651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558000600687590534166201 1918500450515692900624651)
              ·
                refine ⟨2877750675773539350936977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918500450515692900624651 2877750675773539350936977)
                ·
                  refine ⟨2158313006830154513202733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877750675773539350936977 2158313006830154513202733)
                  ·
                    refine ⟨809367377561307942451025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2158313006830154513202733 809367377561307942451025)
                    ·
                      refine ⟨607025533170980956838269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809367377561307942451025 607025533170980956838269)
                      ·
                        rfl

theorem cell23_1182178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1182178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182178 prefixEnd_1182178 := by exact prefixLift 1182178
  have htrace : WordTrace (prefixWord ++ tailWord_1182178) baseStart_1182178 baseEnd_1182178 := by
    simpa [prefixWord, tailWord_1182178, baseEnd_1182178] using wordTrace_append hprefix tailTrace_1182178
  have hstable : (prefixWord ++ tailWord_1182178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182178).length < 2 ^ (prefixWord ++ tailWord_1182178).sum := by decide
  have hdescent : baseEnd_1182178 < baseStart_1182178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182194 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1182194 : Nat := 118140960795 + 1182194 * 2 ^ 59
def prefixEnd_1182194 : Nat := 4983230072969 + 3 ^ 40 * 1182194 * 2
def baseEnd_1182194 : Nat := 607033748861452894238195

theorem tailTrace_1182194 : CollatzResearch.WordTrace tailWord_1182194 prefixEnd_1182194 607033748861452894238195 := by
  unfold tailWord_1182194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10779539369780128876504409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28745438319413677004011757 10779539369780128876504409)
  ·
    refine ⟨8084654527335096657378307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10779539369780128876504409 8084654527335096657378307)
    ·
      refine ⟨12126981791002644986067461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084654527335096657378307 12126981791002644986067461)
      ·
        refine ⟨2273809085812995934887649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12126981791002644986067461 2273809085812995934887649)
        ·
          refine ⟨1705356814359746951165737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273809085812995934887649 1705356814359746951165737)
          ·
            refine ⟨1279017610769810213374303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705356814359746951165737 1279017610769810213374303)
            ·
              refine ⟨1918526416154715320061455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279017610769810213374303 1918526416154715320061455)
              ·
                refine ⟨2877789624232072980092183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918526416154715320061455 2877789624232072980092183)
                ·
                  refine ⟨4316684436348109470138275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877789624232072980092183 4316684436348109470138275)
                  ·
                    refine ⟨6475026654522164205207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4316684436348109470138275 6475026654522164205207413)
                    ·
                      refine ⟨607033748861452894238195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6475026654522164205207413 607033748861452894238195)
                      ·
                        rfl

theorem cell23_1182194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1182194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182194 prefixEnd_1182194 := by exact prefixLift 1182194
  have htrace : WordTrace (prefixWord ++ tailWord_1182194) baseStart_1182194 baseEnd_1182194 := by
    simpa [prefixWord, tailWord_1182194, baseEnd_1182194] using wordTrace_append hprefix tailTrace_1182194
  have hstable : (prefixWord ++ tailWord_1182194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182194).length < 2 ^ (prefixWord ++ tailWord_1182194).sum := by decide
  have hdescent : baseEnd_1182194 < baseStart_1182194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182197 : List Nat := [1, 3, 5, 1, 3, 10]
def baseStart_1182197 : Nat := 118140960795 + 1182197 * 2 ^ 59
def prefixEnd_1182197 : Nat := 4983230072969 + 3 ^ 40 * 1182197 * 2
def baseEnd_1182197 : Nat := 2498087610302125030867

theorem tailTrace_1182197 : CollatzResearch.WordTrace tailWord_1182197 prefixEnd_1182197 2498087610302125030867 := by
  unfold tailWord_1182197
  simp only [CollatzResearch.WordTrace]
  refine ⟨43118266898109647018376845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28745511265406431345584563 43118266898109647018376845)
  ·
    refine ⟨16169350086791117631891317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43118266898109647018376845 16169350086791117631891317)
    ·
      refine ⟨1515876570636667277989811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16169350086791117631891317 1515876570636667277989811)
      ·
        refine ⟨2273814855955000916984717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515876570636667277989811 2273814855955000916984717)
        ·
          refine ⟨852680570983125343869269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2273814855955000916984717 852680570983125343869269)
          ·
            refine ⟨2498087610302125030867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 852680570983125343869269 2498087610302125030867)
            ·
              rfl

theorem cell23_1182197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 10].length) (baseStart_1182197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182197 prefixEnd_1182197 := by exact prefixLift 1182197
  have htrace : WordTrace (prefixWord ++ tailWord_1182197) baseStart_1182197 baseEnd_1182197 := by
    simpa [prefixWord, tailWord_1182197, baseEnd_1182197] using wordTrace_append hprefix tailTrace_1182197
  have hstable : (prefixWord ++ tailWord_1182197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182197).length < 2 ^ (prefixWord ++ tailWord_1182197).sum := by decide
  have hdescent : baseEnd_1182197 < baseStart_1182197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182221 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1182221 : Nat := 118140960795 + 1182221 * 2 ^ 59
def prefixEnd_1182221 : Nat := 4983230072969 + 3 ^ 40 * 1182221 * 2
def baseEnd_1182221 : Nat := 607047612839124288600571

theorem tailTrace_1182221 : CollatzResearch.WordTrace tailWord_1182221 prefixEnd_1182221 607047612839124288600571 := by
  unfold tailWord_1182221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43119142250022699117250517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28746094833348466078167011 43119142250022699117250517)
  ·
    refine ⟨1010604896484907010560559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43119142250022699117250517 1010604896484907010560559)
    ·
      refine ⟨1515907344727360515840839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010604896484907010560559 1515907344727360515840839)
      ·
        refine ⟨2273861017091040773761259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515907344727360515840839 2273861017091040773761259)
        ·
          refine ⟨3410791525636561160641889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273861017091040773761259 3410791525636561160641889)
          ·
            refine ⟨2558093644227420870481417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3410791525636561160641889 2558093644227420870481417)
            ·
              refine ⟨1918570233170565652861063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558093644227420870481417 1918570233170565652861063)
              ·
                refine ⟨2877855349755848479291595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918570233170565652861063 2877855349755848479291595)
                ·
                  refine ⟨4316783024633772718937393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877855349755848479291595 4316783024633772718937393)
                  ·
                    refine ⟨3237587268475329539203045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316783024633772718937393 3237587268475329539203045)
                    ·
                      refine ⟨607047612839124288600571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3237587268475329539203045 607047612839124288600571)
                      ·
                        rfl

theorem cell23_1182221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1182221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182221 prefixEnd_1182221 := by exact prefixLift 1182221
  have htrace : WordTrace (prefixWord ++ tailWord_1182221) baseStart_1182221 baseEnd_1182221 := by
    simpa [prefixWord, tailWord_1182221, baseEnd_1182221] using wordTrace_append hprefix tailTrace_1182221
  have hstable : (prefixWord ++ tailWord_1182221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182221).length < 2 ^ (prefixWord ++ tailWord_1182221).sum := by decide
  have hdescent : baseEnd_1182221 < baseStart_1182221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182223 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 1, 8]
def baseStart_1182223 : Nat := 118140960795 + 1182223 * 2 ^ 59
def prefixEnd_1182223 : Nat := 4983230072969 + 3 ^ 40 * 1182223 * 2
def baseEnd_1182223 : Nat := 202349546600144426925187

theorem tailTrace_1182223 : CollatzResearch.WordTrace tailWord_1182223 prefixEnd_1182223 202349546600144426925187 := by
  unfold tailWord_1182223
  simp only [CollatzResearch.WordTrace]
  refine ⟨43119215196015453458823323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28746143464010302305882215 43119215196015453458823323)
  ·
    refine ⟨64678822794023180188234985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43119215196015453458823323 64678822794023180188234985)
    ·
      refine ⟨48509117095517385141176239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64678822794023180188234985 48509117095517385141176239)
      ·
        refine ⟨72763675643276077711764359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48509117095517385141176239 72763675643276077711764359)
        ·
          refine ⟨109145513464914116567646539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72763675643276077711764359 109145513464914116567646539)
          ·
            refine ⟨163718270197371174851469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109145513464914116567646539 163718270197371174851469809)
            ·
              refine ⟨122788702648028381138602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163718270197371174851469809 122788702648028381138602357)
              ·
                refine ⟨11511440873252660731743971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122788702648028381138602357 11511440873252660731743971)
                ·
                  refine ⟨17267161309878991097615957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11511440873252660731743971 17267161309878991097615957)
                  ·
                    refine ⟨202349546600144426925187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17267161309878991097615957 202349546600144426925187)
                    ·
                      rfl

theorem cell23_1182223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_1182223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182223 prefixEnd_1182223 := by exact prefixLift 1182223
  have htrace : WordTrace (prefixWord ++ tailWord_1182223) baseStart_1182223 baseEnd_1182223 := by
    simpa [prefixWord, tailWord_1182223, baseEnd_1182223] using wordTrace_append hprefix tailTrace_1182223
  have hstable : (prefixWord ++ tailWord_1182223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182223).length < 2 ^ (prefixWord ++ tailWord_1182223).sum := by decide
  have hdescent : baseEnd_1182223 < baseStart_1182223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182264 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_1182264 : Nat := 118140960795 + 1182264 * 2 ^ 59
def prefixEnd_1182264 : Nat := 4983230072969 + 3 ^ 40 * 1182264 * 2
def baseEnd_1182264 : Nat := 607069692507267620362873

theorem tailTrace_1182264 : CollatzResearch.WordTrace tailWord_1182264 prefixEnd_1182264 607069692507267620362873 := by
  unfold tailWord_1182264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21560355294433458730532923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28747140392577944974043897 21560355294433458730532923)
  ·
    refine ⟨32340532941650188095799385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21560355294433458730532923 32340532941650188095799385)
    ·
      refine ⟨24255399706237641071849539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32340532941650188095799385 24255399706237641071849539)
      ·
        refine ⟨36383099559356461607774309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24255399706237641071849539 36383099559356461607774309)
        ·
          refine ⟨6821831167379336551457683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36383099559356461607774309 6821831167379336551457683)
          ·
            refine ⟨10232746751069004827186525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821831167379336551457683 10232746751069004827186525)
            ·
              refine ⟨3837280031650876810194947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10232746751069004827186525 3837280031650876810194947)
              ·
                refine ⟨5755920047476315215292421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837280031650876810194947 5755920047476315215292421)
                ·
                  refine ⟨1079235008901809102867329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5755920047476315215292421 1079235008901809102867329)
                  ·
                    refine ⟨809426256676356827150497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1079235008901809102867329 809426256676356827150497)
                    ·
                      refine ⟨607069692507267620362873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809426256676356827150497 607069692507267620362873)
                      ·
                        rfl

theorem cell23_1182264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_1182264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182264 prefixEnd_1182264 := by exact prefixLift 1182264
  have htrace : WordTrace (prefixWord ++ tailWord_1182264) baseStart_1182264 baseEnd_1182264 := by
    simpa [prefixWord, tailWord_1182264, baseEnd_1182264] using wordTrace_append hprefix tailTrace_1182264
  have hstable : (prefixWord ++ tailWord_1182264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182264).length < 2 ^ (prefixWord ++ tailWord_1182264).sum := by decide
  have hdescent : baseEnd_1182264 < baseStart_1182264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182317 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1182317 : Nat := 118140960795 + 1182317 * 2 ^ 59
def prefixEnd_1182317 : Nat := 4983230072969 + 3 ^ 40 * 1182317 * 2
def baseEnd_1182317 : Nat := 202365635660651971000043

theorem tailTrace_1182317 : CollatzResearch.WordTrace tailWord_1182317 prefixEnd_1182317 202365635660651971000043 := by
  unfold tailWord_1182317
  simp only [CollatzResearch.WordTrace]
  refine ⟨43122643657674907512745205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28748429105116605008496803 43122643657674907512745205)
  ·
    refine ⟨4042747842907022579319863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43122643657674907512745205 4042747842907022579319863)
    ·
      refine ⟨6064121764360533868979795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4042747842907022579319863 6064121764360533868979795)
      ·
        refine ⟨9096182646540800803469693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6064121764360533868979795 9096182646540800803469693)
        ·
          refine ⟨3411068492452800301301135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9096182646540800803469693 3411068492452800301301135)
          ·
            refine ⟨5116602738679200451951703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411068492452800301301135 5116602738679200451951703)
            ·
              refine ⟨7674904108018800677927555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116602738679200451951703 7674904108018800677927555)
              ·
                refine ⟨11512356162028201016891333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674904108018800677927555 11512356162028201016891333)
                ·
                  refine ⟨2158566780380287690667125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11512356162028201016891333 2158566780380287690667125)
                  ·
                    refine ⟨202365635660651971000043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2158566780380287690667125 202365635660651971000043)
                    ·
                      rfl

theorem cell23_1182317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1182317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182317 prefixEnd_1182317 := by exact prefixLift 1182317
  have htrace : WordTrace (prefixWord ++ tailWord_1182317) baseStart_1182317 baseEnd_1182317 := by
    simpa [prefixWord, tailWord_1182317, baseEnd_1182317] using wordTrace_append hprefix tailTrace_1182317
  have hstable : (prefixWord ++ tailWord_1182317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182317).length < 2 ^ (prefixWord ++ tailWord_1182317).sum := by decide
  have hdescent : baseEnd_1182317 < baseStart_1182317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182337 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1182337 : Nat := 118140960795 + 1182337 * 2 ^ 59
def prefixEnd_1182337 : Nat := 4983230072969 + 3 ^ 40 * 1182337 * 2
def baseEnd_1182337 : Nat := 607107176595045834750037

theorem tailTrace_1182337 : CollatzResearch.WordTrace tailWord_1182337 prefixEnd_1182337 607107176595045834750037 := by
  unfold tailWord_1182337
  simp only [CollatzResearch.WordTrace]
  refine ⟨43123373117602450928473265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28748915411734967285648843 43123373117602450928473265)
  ·
    refine ⟨32342529838201838196354949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43123373117602450928473265 32342529838201838196354949)
    ·
      refine ⟨6064224344662844661816553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32342529838201838196354949 6064224344662844661816553)
      ·
        refine ⟨4548168258497133496362415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064224344662844661816553 4548168258497133496362415)
        ·
          refine ⟨6822252387745700244543623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548168258497133496362415 6822252387745700244543623)
          ·
            refine ⟨10233378581618550366815435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822252387745700244543623 10233378581618550366815435)
            ·
              refine ⟨15350067872427825550223153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10233378581618550366815435 15350067872427825550223153)
              ·
                refine ⟨11512550904320869162667365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15350067872427825550223153 11512550904320869162667365)
                ·
                  refine ⟨2158603294560162968000131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11512550904320869162667365 2158603294560162968000131)
                  ·
                    refine ⟨3237904941840244452000197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158603294560162968000131 3237904941840244452000197)
                    ·
                      refine ⟨607107176595045834750037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3237904941840244452000197 607107176595045834750037)
                      ·
                        rfl

theorem cell23_1182337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1182337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182337 prefixEnd_1182337 := by exact prefixLift 1182337
  have htrace : WordTrace (prefixWord ++ tailWord_1182337) baseStart_1182337 baseEnd_1182337 := by
    simpa [prefixWord, tailWord_1182337, baseEnd_1182337] using wordTrace_append hprefix tailTrace_1182337
  have hstable : (prefixWord ++ tailWord_1182337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182337).length < 2 ^ (prefixWord ++ tailWord_1182337).sum := by decide
  have hdescent : baseEnd_1182337 < baseStart_1182337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182354 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1182354 : Nat := 118140960795 + 1182354 * 2 ^ 59
def prefixEnd_1182354 : Nat := 4983230072969 + 3 ^ 40 * 1182354 * 2
def baseEnd_1182354 : Nat := 607115905766172268237459

theorem tailTrace_1182354 : CollatzResearch.WordTrace tailWord_1182354 prefixEnd_1182354 607115905766172268237459 := by
  unfold tailWord_1182354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10780998289635215707960529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28749328772360575221228077 10780998289635215707960529)
  ·
    refine ⟨8085748717226411780970397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10780998289635215707960529 8085748717226411780970397)
    ·
      refine ⟨3032155768959904417863899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8085748717226411780970397 3032155768959904417863899)
      ·
        refine ⟨4548233653439856626795849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032155768959904417863899 4548233653439856626795849)
        ·
          refine ⟨3411175240079892470096887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548233653439856626795849 3411175240079892470096887)
          ·
            refine ⟨5116762860119838705145331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411175240079892470096887 5116762860119838705145331)
            ·
              refine ⟨7675144290179758057717997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116762860119838705145331 7675144290179758057717997)
              ·
                refine ⟨2878179108817409271644249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7675144290179758057717997 2878179108817409271644249)
                ·
                  refine ⟨2158634331613056953733187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878179108817409271644249 2158634331613056953733187)
                  ·
                    refine ⟨3237951497419585430599781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158634331613056953733187 3237951497419585430599781)
                    ·
                      refine ⟨607115905766172268237459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3237951497419585430599781 607115905766172268237459)
                      ·
                        rfl

theorem cell23_1182354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1182354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182354 prefixEnd_1182354 := by exact prefixLift 1182354
  have htrace : WordTrace (prefixWord ++ tailWord_1182354) baseStart_1182354 baseEnd_1182354 := by
    simpa [prefixWord, tailWord_1182354, baseEnd_1182354] using wordTrace_append hprefix tailTrace_1182354
  have hstable : (prefixWord ++ tailWord_1182354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182354).length < 2 ^ (prefixWord ++ tailWord_1182354).sum := by decide
  have hdescent : baseEnd_1182354 < baseStart_1182354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182424 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 1, 5]
def baseStart_1182424 : Nat := 118140960795 + 1182424 * 2 ^ 59
def prefixEnd_1182424 : Nat := 4983230072969 + 3 ^ 40 * 1182424 * 2
def baseEnd_1182424 : Nat := 202383949803995664787379

theorem tailTrace_1182424 : CollatzResearch.WordTrace tailWord_1182424 prefixEnd_1182424 202383949803995664787379 := by
  unfold tailWord_1182424
  simp only [CollatzResearch.WordTrace]
  refine ⟨21563273134143632393445163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28751030845524843191260217 21563273134143632393445163)
  ·
    refine ⟨32344909701215448590167745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21563273134143632393445163 32344909701215448590167745)
    ·
      refine ⟨24258682275911586442625809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32344909701215448590167745 24258682275911586442625809)
      ·
        refine ⟨18194011706933689831969357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24258682275911586442625809 18194011706933689831969357)
        ·
          refine ⟨6822754390100133686988509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18194011706933689831969357 6822754390100133686988509)
          ·
            refine ⟨2558532896287550132620691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6822754390100133686988509 2558532896287550132620691)
            ·
              refine ⟨3837799344431325198931037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558532896287550132620691 3837799344431325198931037)
              ·
                refine ⟨1439174754161746949599139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3837799344431325198931037 1439174754161746949599139)
                ·
                  refine ⟨2158762131242620424398709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439174754161746949599139 2158762131242620424398709)
                  ·
                    refine ⟨202383949803995664787379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2158762131242620424398709 202383949803995664787379)
                    ·
                      rfl

theorem cell23_1182424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_1182424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182424 prefixEnd_1182424 := by exact prefixLift 1182424
  have htrace : WordTrace (prefixWord ++ tailWord_1182424) baseStart_1182424 baseEnd_1182424 := by
    simpa [prefixWord, tailWord_1182424, baseEnd_1182424] using wordTrace_append hprefix tailTrace_1182424
  have hstable : (prefixWord ++ tailWord_1182424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182424).length < 2 ^ (prefixWord ++ tailWord_1182424).sum := by decide
  have hdescent : baseEnd_1182424 < baseStart_1182424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182447 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_1182447 : Nat := 118140960795 + 1182447 * 2 ^ 59
def prefixEnd_1182447 : Nat := 4983230072969 + 3 ^ 40 * 1182447 * 2
def baseEnd_1182447 : Nat := 607163659467040404374531

theorem tailTrace_1182447 : CollatzResearch.WordTrace tailWord_1182447 prefixEnd_1182447 607163659467040404374531 := by
  unfold tailWord_1182447
  simp only [CollatzResearch.WordTrace]
  refine ⟨43127385147203939714977595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28751590098135959809985063 43127385147203939714977595)
  ·
    refine ⟨64691077720805909572466393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43127385147203939714977595 64691077720805909572466393)
    ·
      refine ⟨48518308290604432179349795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64691077720805909572466393 48518308290604432179349795)
      ·
        refine ⟨72777462435906648269024693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48518308290604432179349795 72777462435906648269024693)
        ·
          refine ⟨6822887103366248275221065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72777462435906648269024693 6822887103366248275221065)
          ·
            refine ⟨5117165327524686206415799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822887103366248275221065 5117165327524686206415799)
            ·
              refine ⟨7675747991287029309623699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117165327524686206415799 7675747991287029309623699)
              ·
                refine ⟨11513621986930543964435549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7675747991287029309623699 11513621986930543964435549)
                ·
                  refine ⟨4317608245098953986663331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11513621986930543964435549 4317608245098953986663331)
                  ·
                    refine ⟨6476412367648430979994997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4317608245098953986663331 6476412367648430979994997)
                    ·
                      refine ⟨607163659467040404374531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6476412367648430979994997 607163659467040404374531)
                      ·
                        rfl

theorem cell23_1182447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_1182447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182447 prefixEnd_1182447 := by exact prefixLift 1182447
  have htrace : WordTrace (prefixWord ++ tailWord_1182447) baseStart_1182447 baseEnd_1182447 := by
    simpa [prefixWord, tailWord_1182447, baseEnd_1182447] using wordTrace_append hprefix tailTrace_1182447
  have hstable : (prefixWord ++ tailWord_1182447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182447).length < 2 ^ (prefixWord ++ tailWord_1182447).sum := by decide
  have hdescent : baseEnd_1182447 < baseStart_1182447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182461 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_1182461 : Nat := 118140960795 + 1182461 * 2 ^ 59
def prefixEnd_1182461 : Nat := 4983230072969 + 3 ^ 40 * 1182461 * 2
def baseEnd_1182461 : Nat := 607170848196203349599467

theorem tailTrace_1182461 : CollatzResearch.WordTrace tailWord_1182461 prefixEnd_1182461 607170848196203349599467 := by
  unfold tailWord_1182461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43127895769153220105987237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28751930512768813403991491 43127895769153220105987237)
  ·
    refine ⟨8086480456716228769872607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43127895769153220105987237 8086480456716228769872607)
    ·
      refine ⟨12129720685074343154808911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8086480456716228769872607 12129720685074343154808911)
      ·
        refine ⟨18194581027611514732213367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12129720685074343154808911 18194581027611514732213367)
        ·
          refine ⟨27291871541417272098320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18194581027611514732213367 27291871541417272098320051)
          ·
            refine ⟨40937807312125908147480077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27291871541417272098320051 40937807312125908147480077)
            ·
              refine ⟨15351677742047215555305029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40937807312125908147480077 15351677742047215555305029)
              ·
                refine ⟨2878439576633852916619693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15351677742047215555305029 2878439576633852916619693)
                ·
                  refine ⟨1079414841237694843732385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2878439576633852916619693 1079414841237694843732385)
                  ·
                    refine ⟨809561130928271132799289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1079414841237694843732385 809561130928271132799289)
                    ·
                      refine ⟨607170848196203349599467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809561130928271132799289 607170848196203349599467)
                      ·
                        rfl

theorem cell23_1182461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_1182461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182461 prefixEnd_1182461 := by exact prefixLift 1182461
  have htrace : WordTrace (prefixWord ++ tailWord_1182461) baseStart_1182461 baseEnd_1182461 := by
    simpa [prefixWord, tailWord_1182461, baseEnd_1182461] using wordTrace_append hprefix tailTrace_1182461
  have hstable : (prefixWord ++ tailWord_1182461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182461).length < 2 ^ (prefixWord ++ tailWord_1182461).sum := by decide
  have hdescent : baseEnd_1182461 < baseStart_1182461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182497 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1182497 : Nat := 118140960795 + 1182497 * 2 ^ 59
def prefixEnd_1182497 : Nat := 4983230072969 + 3 ^ 40 * 1182497 * 2
def baseEnd_1182497 : Nat := 202396444499921736249767

theorem tailTrace_1182497 : CollatzResearch.WordTrace tailWord_1182497 prefixEnd_1182497 202396444499921736249767 := by
  unfold tailWord_1182497
  simp only [CollatzResearch.WordTrace]
  refine ⟨43129208797022798254297745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28752805864681865502865163 43129208797022798254297745)
  ·
    refine ⟨32346906597767098690723309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43129208797022798254297745 32346906597767098690723309)
    ·
      refine ⟨12130089974162662009021241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32346906597767098690723309 12130089974162662009021241)
      ·
        refine ⟨9097567480621996506765931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12130089974162662009021241 9097567480621996506765931)
        ·
          refine ⟨13646351220932994760148897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097567480621996506765931 13646351220932994760148897)
          ·
            refine ⟨10234763415699746070111673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13646351220932994760148897 10234763415699746070111673)
            ·
              refine ⟨7676072561774809552583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10234763415699746070111673 7676072561774809552583755)
              ·
                refine ⟨11514108842662214328875633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676072561774809552583755 11514108842662214328875633)
                ·
                  refine ⟨8635581631996660746656725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11514108842662214328875633 8635581631996660746656725)
                  ·
                    refine ⟨202396444499921736249767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8635581631996660746656725 202396444499921736249767)
                    ·
                      rfl

theorem cell23_1182497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1182497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182497 prefixEnd_1182497 := by exact prefixLift 1182497
  have htrace : WordTrace (prefixWord ++ tailWord_1182497) baseStart_1182497 baseEnd_1182497 := by
    simpa [prefixWord, tailWord_1182497, baseEnd_1182497] using wordTrace_append hprefix tailTrace_1182497
  have hstable : (prefixWord ++ tailWord_1182497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182497).length < 2 ^ (prefixWord ++ tailWord_1182497).sum := by decide
  have hdescent : baseEnd_1182497 < baseStart_1182497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182532 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1182532 : Nat := 118140960795 + 1182532 * 2 ^ 59
def prefixEnd_1182532 : Nat := 4983230072969 + 3 ^ 40 * 1182532 * 2
def baseEnd_1182532 : Nat := 607207305322672571811641

theorem tailTrace_1182532 : CollatzResearch.WordTrace tailWord_1182532 prefixEnd_1182532 607207305322672571811641 := by
  unfold tailWord_1182532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565242675947999615910925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28753656901263999487881233 21565242675947999615910925)
  ·
    refine ⟨8086966003480499855966597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21565242675947999615910925 8086966003480499855966597)
    ·
      refine ⟨1516306125652593722993737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8086966003480499855966597 1516306125652593722993737)
      ·
        refine ⟨1137229594239445292245303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1516306125652593722993737 1137229594239445292245303)
        ·
          refine ⟨1705844391359167938367955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137229594239445292245303 1705844391359167938367955)
          ·
            refine ⟨2558766587038751907551933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705844391359167938367955 2558766587038751907551933)
            ·
              refine ⟨959537470139531965331975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2558766587038751907551933 959537470139531965331975)
              ·
                refine ⟨1439306205209297947997963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959537470139531965331975 1439306205209297947997963)
                ·
                  refine ⟨2158959307813946921996945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439306205209297947997963 2158959307813946921996945)
                  ·
                    refine ⟨1619219480860460191497709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158959307813946921996945 1619219480860460191497709)
                    ·
                      refine ⟨607207305322672571811641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619219480860460191497709 607207305322672571811641)
                      ·
                        rfl

theorem cell23_1182532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1182532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182532 prefixEnd_1182532 := by exact prefixLift 1182532
  have htrace : WordTrace (prefixWord ++ tailWord_1182532) baseStart_1182532 baseEnd_1182532 := by
    simpa [prefixWord, tailWord_1182532, baseEnd_1182532] using wordTrace_append hprefix tailTrace_1182532
  have hstable : (prefixWord ++ tailWord_1182532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182532).length < 2 ^ (prefixWord ++ tailWord_1182532).sum := by decide
  have hdescent : baseEnd_1182532 < baseStart_1182532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182547 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_1182547 : Nat := 118140960795 + 1182547 * 2 ^ 59
def prefixEnd_1182547 : Nat := 4983230072969 + 3 ^ 40 * 1182547 * 2
def baseEnd_1182547 : Nat := 607215007532490013124071

theorem tailTrace_1182547 : CollatzResearch.WordTrace tailWord_1182547 prefixEnd_1182547 607215007532490013124071 := by
  unfold tailWord_1182547
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131032446841656793617895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28754021631227771195745263 43131032446841656793617895)
  ·
    refine ⟨64696548670262485190426843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43131032446841656793617895 64696548670262485190426843)
    ·
      refine ⟨97044823005393727785640265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64696548670262485190426843 97044823005393727785640265)
      ·
        refine ⟨72783617254045295839230199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97044823005393727785640265 72783617254045295839230199)
        ·
          refine ⟨109175425881067943758845299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72783617254045295839230199 109175425881067943758845299)
          ·
            refine ⟨163763138821601915638267949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109175425881067943758845299 163763138821601915638267949)
            ·
              refine ⟨61411177058100718364350481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163763138821601915638267949 61411177058100718364350481)
              ·
                refine ⟨46058382793575538773262861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61411177058100718364350481 46058382793575538773262861)
                ·
                  refine ⟨17271893547590827039973573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46058382793575538773262861 17271893547590827039973573)
                  ·
                    refine ⟨3238480040173280069995045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17271893547590827039973573 3238480040173280069995045)
                    ·
                      refine ⟨607215007532490013124071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3238480040173280069995045 607215007532490013124071)
                      ·
                        rfl

theorem cell23_1182547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_1182547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182547 prefixEnd_1182547 := by exact prefixLift 1182547
  have htrace : WordTrace (prefixWord ++ tailWord_1182547) baseStart_1182547 baseEnd_1182547 := by
    simpa [prefixWord, tailWord_1182547, baseEnd_1182547] using wordTrace_append hprefix tailTrace_1182547
  have hstable : (prefixWord ++ tailWord_1182547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182547).length < 2 ^ (prefixWord ++ tailWord_1182547).sum := by decide
  have hdescent : baseEnd_1182547 < baseStart_1182547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182554 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1182554 : Nat := 118140960795 + 1182554 * 2 ^ 59
def prefixEnd_1182554 : Nat := 4983230072969 + 3 ^ 40 * 1182554 * 2
def baseEnd_1182554 : Nat := 607218601897071485736539

theorem tailTrace_1182554 : CollatzResearch.WordTrace tailWord_1182554 prefixEnd_1182554 607218601897071485736539 := by
  unfold tailWord_1182554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782821939454074247280679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28754191838544197992748477 10782821939454074247280679)
  ·
    refine ⟨16174232909181111370921019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10782821939454074247280679 16174232909181111370921019)
    ·
      refine ⟨24261349363771667056381529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16174232909181111370921019 24261349363771667056381529)
      ·
        refine ⟨18196012022828750292286147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24261349363771667056381529 18196012022828750292286147)
        ·
          refine ⟨27294018034243125438429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18196012022828750292286147 27294018034243125438429221)
          ·
            refine ⟨5117628381420586019705479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27294018034243125438429221 5117628381420586019705479)
            ·
              refine ⟨7676442572130879029558219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117628381420586019705479 7676442572130879029558219)
              ·
                refine ⟨11514663858196318544337329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676442572130879029558219 11514663858196318544337329)
                ·
                  refine ⟨8635997893647238908252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11514663858196318544337329 8635997893647238908252997)
                  ·
                    refine ⟨1619249605058857295297437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8635997893647238908252997 1619249605058857295297437)
                    ·
                      refine ⟨607218601897071485736539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619249605058857295297437 607218601897071485736539)
                      ·
                        rfl

theorem cell23_1182554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1182554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182554 prefixEnd_1182554 := by exact prefixLift 1182554
  have htrace : WordTrace (prefixWord ++ tailWord_1182554) baseStart_1182554 baseEnd_1182554 := by
    simpa [prefixWord, tailWord_1182554, baseEnd_1182554] using wordTrace_append hprefix tailTrace_1182554
  have hstable : (prefixWord ++ tailWord_1182554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182554).length < 2 ^ (prefixWord ++ tailWord_1182554).sum := by decide
  have hdescent : baseEnd_1182554 < baseStart_1182554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182564 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1182564 : Nat := 118140960795 + 1182564 * 2 ^ 59
def prefixEnd_1182564 : Nat := 4983230072969 + 3 ^ 40 * 1182564 * 2
def baseEnd_1182564 : Nat := 607223736703616446611493

theorem tailTrace_1182564 : CollatzResearch.WordTrace tailWord_1182564 prefixEnd_1182564 607223736703616446611493 := by
  unfold tailWord_1182564
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565826243890034348493373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28754434991853379131324497 21565826243890034348493373)
  ·
    refine ⟨8087184841458762880685015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21565826243890034348493373 8087184841458762880685015)
    ·
      refine ⟨12130777262188144321027523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8087184841458762880685015 12130777262188144321027523)
      ·
        refine ⟨18196165893282216481541285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12130777262188144321027523 18196165893282216481541285)
        ·
          refine ⟨3411781104990415590288991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18196165893282216481541285 3411781104990415590288991)
          ·
            refine ⟨5117671657485623385433487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411781104990415590288991 5117671657485623385433487)
            ·
              refine ⟨7676507486228435078150231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117671657485623385433487 7676507486228435078150231)
              ·
                refine ⟨11514761229342652617225347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676507486228435078150231 11514761229342652617225347)
                ·
                  refine ⟨17272141844013978925838021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11514761229342652617225347 17272141844013978925838021)
                  ·
                    refine ⟨3238526595752621048594629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17272141844013978925838021 3238526595752621048594629)
                    ·
                      refine ⟨607223736703616446611493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3238526595752621048594629 607223736703616446611493)
                      ·
                        rfl

theorem cell23_1182564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1182564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182564 prefixEnd_1182564 := by exact prefixLift 1182564
  have htrace : WordTrace (prefixWord ++ tailWord_1182564) baseStart_1182564 baseEnd_1182564 := by
    simpa [prefixWord, tailWord_1182564, baseEnd_1182564] using wordTrace_append hprefix tailTrace_1182564
  have hstable : (prefixWord ++ tailWord_1182564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182564).length < 2 ^ (prefixWord ++ tailWord_1182564).sum := by decide
  have hdescent : baseEnd_1182564 < baseStart_1182564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182568 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1182568 : Nat := 118140960795 + 1182568 * 2 ^ 59
def prefixEnd_1182568 : Nat := 4983230072969 + 3 ^ 40 * 1182568 * 2
def baseEnd_1182568 : Nat := 607225790626234430961475

theorem tailTrace_1182568 : CollatzResearch.WordTrace tailWord_1182568 prefixEnd_1182568 607225790626234430961475 := by
  unfold tailWord_1182568
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565899189882788690066179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28754532253177051586754905 21565899189882788690066179)
  ·
    refine ⟨32348848784824183035099269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21565899189882788690066179 32348848784824183035099269)
    ·
      refine ⟨6065409147154534319081113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32348848784824183035099269 6065409147154534319081113)
      ·
        refine ⟨4549056860365900739310835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6065409147154534319081113 4549056860365900739310835)
        ·
          refine ⟨6823585290548851108966253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549056860365900739310835 6823585290548851108966253)
          ·
            refine ⟨2558844483955819165862345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6823585290548851108966253 2558844483955819165862345)
            ·
              refine ⟨1919133362966864374396759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558844483955819165862345 1919133362966864374396759)
              ·
                refine ⟨2878700044450296561595139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919133362966864374396759 2878700044450296561595139)
                ·
                  refine ⟨4318050066675444842392709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878700044450296561595139 4318050066675444842392709)
                  ·
                    refine ⟨809634387501645907948633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318050066675444842392709 809634387501645907948633)
                    ·
                      refine ⟨607225790626234430961475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809634387501645907948633 607225790626234430961475)
                      ·
                        rfl

theorem cell23_1182568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1182568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182568 prefixEnd_1182568 := by exact prefixLift 1182568
  have htrace : WordTrace (prefixWord ++ tailWord_1182568) baseStart_1182568 baseEnd_1182568 := by
    simpa [prefixWord, tailWord_1182568, baseEnd_1182568] using wordTrace_append hprefix tailTrace_1182568
  have hstable : (prefixWord ++ tailWord_1182568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182568).length < 2 ^ (prefixWord ++ tailWord_1182568).sum := by decide
  have hdescent : baseEnd_1182568 < baseStart_1182568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182602 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1182602 : Nat := 118140960795 + 1182602 * 2 ^ 59
def prefixEnd_1182602 : Nat := 4983230072969 + 3 ^ 40 * 1182602 * 2
def baseEnd_1182602 : Nat := 607243248968487297936319

theorem tailTrace_1182602 : CollatzResearch.WordTrace tailWord_1182602 prefixEnd_1182602 607243248968487297936319 := by
  unfold tailWord_1182602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783259615410600296717515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28755358974428267457913373 10783259615410600296717515)
  ·
    refine ⟨16174889423115900445076273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10783259615410600296717515 16174889423115900445076273)
    ·
      refine ⟨12131167067336925333807205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16174889423115900445076273 12131167067336925333807205)
      ·
        refine ⟨2274593825125673500088851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12131167067336925333807205 2274593825125673500088851)
        ·
          refine ⟨3411890737688510250133277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274593825125673500088851 3411890737688510250133277)
          ·
            refine ⟨1279459026633191343799979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3411890737688510250133277 1279459026633191343799979)
            ·
              refine ⟨1919188539949787015699969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279459026633191343799979 1919188539949787015699969)
              ·
                refine ⟨1439391404962340261774977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919188539949787015699969 1439391404962340261774977)
                ·
                  refine ⟨1079543553721755196331233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439391404962340261774977 1079543553721755196331233)
                  ·
                    refine ⟨809657665291316397248425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1079543553721755196331233 809657665291316397248425)
                    ·
                      refine ⟨607243248968487297936319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809657665291316397248425 607243248968487297936319)
                      ·
                        rfl

theorem cell23_1182602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1182602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182602 prefixEnd_1182602 := by exact prefixLift 1182602
  have htrace : WordTrace (prefixWord ++ tailWord_1182602) baseStart_1182602 baseEnd_1182602 := by
    simpa [prefixWord, tailWord_1182602, baseEnd_1182602] using wordTrace_append hprefix tailTrace_1182602
  have hstable : (prefixWord ++ tailWord_1182602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182602).length < 2 ^ (prefixWord ++ tailWord_1182602).sum := by decide
  have hdescent : baseEnd_1182602 < baseStart_1182602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182604 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_1182604 : Nat := 118140960795 + 1182604 * 2 ^ 59
def prefixEnd_1182604 : Nat := 4983230072969 + 3 ^ 40 * 1182604 * 2
def baseEnd_1182604 : Nat := 202414758643265430037103

theorem tailTrace_1182604 : CollatzResearch.WordTrace tailWord_1182604 prefixEnd_1182604 202414758643265430037103 := by
  unfold tailWord_1182604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21566555703817577764221433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28755407605090103685628577 21566555703817577764221433)
  ·
    refine ⟨16174916777863183323166075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21566555703817577764221433 16174916777863183323166075)
    ·
      refine ⟨24262375166794774984749113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16174916777863183323166075 24262375166794774984749113)
      ·
        refine ⟨18196781375096081238561835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24262375166794774984749113 18196781375096081238561835)
        ·
          refine ⟨27295172062644121857842753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18196781375096081238561835 27295172062644121857842753)
          ·
            refine ⟨20471379046983091393382065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27295172062644121857842753 20471379046983091393382065)
            ·
              refine ⟨15353534285237318545036549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20471379046983091393382065 15353534285237318545036549)
              ·
                refine ⟨2878787678481997227194353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15353534285237318545036549 2878787678481997227194353)
                ·
                  refine ⟨2159090758861497920395765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878787678481997227194353 2159090758861497920395765)
                  ·
                    refine ⟨202414758643265430037103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2159090758861497920395765 202414758643265430037103)
                    ·
                      rfl

theorem cell23_1182604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_1182604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182604 prefixEnd_1182604 := by exact prefixLift 1182604
  have htrace : WordTrace (prefixWord ++ tailWord_1182604) baseStart_1182604 baseEnd_1182604 := by
    simpa [prefixWord, tailWord_1182604, baseEnd_1182604] using wordTrace_append hprefix tailTrace_1182604
  have hstable : (prefixWord ++ tailWord_1182604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182604).length < 2 ^ (prefixWord ++ tailWord_1182604).sum := by decide
  have hdescent : baseEnd_1182604 < baseStart_1182604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182624 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1182624 : Nat := 118140960795 + 1182624 * 2 ^ 59
def prefixEnd_1182624 : Nat := 4983230072969 + 3 ^ 40 * 1182624 * 2
def baseEnd_1182624 : Nat := 607254545542886211861217

theorem tailTrace_1182624 : CollatzResearch.WordTrace tailWord_1182624 prefixEnd_1182624 607254545542886211861217 := by
  unfold tailWord_1182624
  simp only [CollatzResearch.WordTrace]
  refine ⟨21566920433781349472085463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28755893911708465962780617 21566920433781349472085463)
  ·
    refine ⟨32350380650672024208128195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21566920433781349472085463 32350380650672024208128195)
    ·
      refine ⟨48525570976008036312192293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32350380650672024208128195 48525570976008036312192293)
      ·
        refine ⟨9098544558001506808536055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48525570976008036312192293 9098544558001506808536055)
        ·
          refine ⟨13647816837002260212804083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098544558001506808536055 13647816837002260212804083)
          ·
            refine ⟨20471725255503390319206125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647816837002260212804083 20471725255503390319206125)
            ·
              refine ⟨7676896970813771369702297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20471725255503390319206125 7676896970813771369702297)
              ·
                refine ⟨5757672728110328527276723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7676896970813771369702297 5757672728110328527276723)
                ·
                  refine ⟨8636509092165492790915085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757672728110328527276723 8636509092165492790915085)
                  ·
                    refine ⟨3238690909562059796593157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8636509092165492790915085 3238690909562059796593157)
                    ·
                      refine ⟨607254545542886211861217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3238690909562059796593157 607254545542886211861217)
                      ·
                        rfl

theorem cell23_1182624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1182624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182624 prefixEnd_1182624 := by exact prefixLift 1182624
  have htrace : WordTrace (prefixWord ++ tailWord_1182624) baseStart_1182624 baseEnd_1182624 := by
    simpa [prefixWord, tailWord_1182624, baseEnd_1182624] using wordTrace_append hprefix tailTrace_1182624
  have hstable : (prefixWord ++ tailWord_1182624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182624).length < 2 ^ (prefixWord ++ tailWord_1182624).sum := by decide
  have hdescent : baseEnd_1182624 < baseStart_1182624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182681 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 6]
def baseStart_1182681 : Nat := 118140960795 + 1182681 * 2 ^ 59
def prefixEnd_1182681 : Nat := 4983230072969 + 3 ^ 40 * 1182681 * 2
def baseEnd_1182681 : Nat := 67475979326688054316495

theorem tailTrace_1182681 : CollatzResearch.WordTrace tailWord_1182681 prefixEnd_1182681 67475979326688054316495 := by
  unfold tailWord_1182681
  simp only [CollatzResearch.WordTrace]
  refine ⟨43135919828356197678995897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28757279885570798452663931 43135919828356197678995897)
  ·
    refine ⟨32351939871267148259246923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43135919828356197678995897 32351939871267148259246923)
    ·
      refine ⟨48527909806900722388870385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32351939871267148259246923 48527909806900722388870385)
      ·
        refine ⟨36395932355175541791652789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48527909806900722388870385 36395932355175541791652789)
        ·
          refine ⟨3412118658297707042967449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36395932355175541791652789 3412118658297707042967449)
          ·
            refine ⟨2559088993723280282225587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412118658297707042967449 2559088993723280282225587)
            ·
              refine ⟨3838633490584920423338381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559088993723280282225587 3838633490584920423338381)
              ·
                refine ⟨1439487558969345158751893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3838633490584920423338381 1439487558969345158751893)
                ·
                  refine ⟨67475979326688054316495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1439487558969345158751893 67475979326688054316495)
                  ·
                    rfl

theorem cell23_1182681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_1182681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182681 prefixEnd_1182681 := by exact prefixLift 1182681
  have htrace : WordTrace (prefixWord ++ tailWord_1182681) baseStart_1182681 baseEnd_1182681 := by
    simpa [prefixWord, tailWord_1182681, baseEnd_1182681] using wordTrace_append hprefix tailTrace_1182681
  have hstable : (prefixWord ++ tailWord_1182681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182681).length < 2 ^ (prefixWord ++ tailWord_1182681).sum := by decide
  have hdescent : baseEnd_1182681 < baseStart_1182681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182725 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_1182725 : Nat := 118140960795 + 1182725 * 2 ^ 59
def prefixEnd_1182725 : Nat := 4983230072969 + 3 ^ 40 * 1182725 * 2
def baseEnd_1182725 : Nat := 607306407088990316698253

theorem tailTrace_1182725 : CollatzResearch.WordTrace tailWord_1182725 prefixEnd_1182725 607306407088990316698253 := by
  unfold tailWord_1182725
  simp only [CollatzResearch.WordTrace]
  refine ⟨43137524640196793193597629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28758349760131195462398419 43137524640196793193597629)
  ·
    refine ⟨16176571740073797447599111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43137524640196793193597629 16176571740073797447599111)
    ·
      refine ⟨24264857610110696171398667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176571740073797447599111 24264857610110696171398667)
      ·
        refine ⟨36397286415166044257098001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264857610110696171398667 36397286415166044257098001)
        ·
          refine ⟨27297964811374533192823501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36397286415166044257098001 27297964811374533192823501)
          ·
            refine ⟨10236736804265449947308813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27297964811374533192823501 10236736804265449947308813)
            ·
              refine ⟨3838776301599543730240805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10236736804265449947308813 3838776301599543730240805)
              ·
                refine ⟨719770556549914449420151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3838776301599543730240805 719770556549914449420151)
                ·
                  refine ⟨1079655834824871674130227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719770556549914449420151 1079655834824871674130227)
                  ·
                    refine ⟨1619483752237307511195341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079655834824871674130227 1619483752237307511195341)
                    ·
                      refine ⟨607306407088990316698253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619483752237307511195341 607306407088990316698253)
                      ·
                        rfl

theorem cell23_1182725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_1182725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182725 prefixEnd_1182725 := by exact prefixLift 1182725
  have htrace : WordTrace (prefixWord ++ tailWord_1182725) baseStart_1182725 baseEnd_1182725 := by
    simpa [prefixWord, tailWord_1182725, baseEnd_1182725] using wordTrace_append hprefix tailTrace_1182725
  have hstable : (prefixWord ++ tailWord_1182725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182725).length < 2 ^ (prefixWord ++ tailWord_1182725).sum := by decide
  have hdescent : baseEnd_1182725 < baseStart_1182725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182731 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4]
def baseStart_1182731 : Nat := 118140960795 + 1182731 * 2 ^ 59
def prefixEnd_1182731 : Nat := 4983230072969 + 3 ^ 40 * 1182731 * 2
def baseEnd_1182731 : Nat := 607309487972917293223225

theorem tailTrace_1182731 : CollatzResearch.WordTrace tailWord_1182731 prefixEnd_1182731 607309487972917293223225 := by
  unfold tailWord_1182731
  simp only [CollatzResearch.WordTrace]
  refine ⟨43137743478175056218316047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28758495652116704145544031 43137743478175056218316047)
  ·
    refine ⟨64706615217262584327474071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43137743478175056218316047 64706615217262584327474071)
    ·
      refine ⟨97059922825893876491211107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64706615217262584327474071 97059922825893876491211107)
      ·
        refine ⟨145589884238840814736816661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97059922825893876491211107 145589884238840814736816661)
        ·
          refine ⟨6824525823695663190788281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145589884238840814736816661 6824525823695663190788281)
          ·
            refine ⟨5118394367771747393091211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6824525823695663190788281 5118394367771747393091211)
            ·
              refine ⟨7677591551657621089636817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118394367771747393091211 7677591551657621089636817)
              ·
                refine ⟨5758193663743215817227613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7677591551657621089636817 5758193663743215817227613)
                ·
                  refine ⟨2159322623903705931460355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5758193663743215817227613 2159322623903705931460355)
                  ·
                    refine ⟨3238983935855558897190533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2159322623903705931460355 3238983935855558897190533)
                    ·
                      refine ⟨607309487972917293223225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3238983935855558897190533 607309487972917293223225)
                      ·
                        rfl

theorem cell23_1182731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_1182731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182731 prefixEnd_1182731 := by exact prefixLift 1182731
  have htrace : WordTrace (prefixWord ++ tailWord_1182731) baseStart_1182731 baseEnd_1182731 := by
    simpa [prefixWord, tailWord_1182731, baseEnd_1182731] using wordTrace_append hprefix tailTrace_1182731
  have hstable : (prefixWord ++ tailWord_1182731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182731).length < 2 ^ (prefixWord ++ tailWord_1182731).sum := by decide
  have hdescent : baseEnd_1182731 < baseStart_1182731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182741 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1182741 : Nat := 118140960795 + 1182741 * 2 ^ 59
def prefixEnd_1182741 : Nat := 4983230072969 + 3 ^ 40 * 1182741 * 2
def baseEnd_1182741 : Nat := 202438207593154084699393

theorem tailTrace_1182741 : CollatzResearch.WordTrace tailWord_1182741 prefixEnd_1182741 202438207593154084699393 := by
  unfold tailWord_1182741
  simp only [CollatzResearch.WordTrace]
  refine ⟨43138108208138827926180077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28758738805425885284120051 43138108208138827926180077)
  ·
    refine ⟨16176790578052060472317529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43138108208138827926180077 16176790578052060472317529)
    ·
      refine ⟨12132592933539045354238147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16176790578052060472317529 12132592933539045354238147)
      ·
        refine ⟨18198889400308568031357221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12132592933539045354238147 18198889400308568031357221)
        ·
          refine ⟨3412291762557856505879479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18198889400308568031357221 3412291762557856505879479)
          ·
            refine ⟨5118437643836784758819219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412291762557856505879479 5118437643836784758819219)
            ·
              refine ⟨7677656465755177138228829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118437643836784758819219 7677656465755177138228829)
              ·
                refine ⟨2879121174658191426835811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7677656465755177138228829 2879121174658191426835811)
                ·
                  refine ⟨4318681761987287140253717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879121174658191426835811 4318681761987287140253717)
                  ·
                    refine ⟨202438207593154084699393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4318681761987287140253717 202438207593154084699393)
                    ·
                      rfl

theorem cell23_1182741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1182741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182741 prefixEnd_1182741 := by exact prefixLift 1182741
  have htrace : WordTrace (prefixWord ++ tailWord_1182741) baseStart_1182741 baseEnd_1182741 := by
    simpa [prefixWord, tailWord_1182741, baseEnd_1182741] using wordTrace_append hprefix tailTrace_1182741
  have hstable : (prefixWord ++ tailWord_1182741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182741).length < 2 ^ (prefixWord ++ tailWord_1182741).sum := by decide
  have hdescent : baseEnd_1182741 < baseStart_1182741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182759 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1182759 : Nat := 118140960795 + 1182759 * 2 ^ 59
def prefixEnd_1182759 : Nat := 4983230072969 + 3 ^ 40 * 1182759 * 2
def baseEnd_1182759 : Nat := 607323865431243183673097

theorem tailTrace_1182759 : CollatzResearch.WordTrace tailWord_1182759 prefixEnd_1182759 607323865431243183673097 := by
  unfold tailWord_1182759
  simp only [CollatzResearch.WordTrace]
  refine ⟨43138764722073617000335331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28759176481382411333556887 43138764722073617000335331)
  ·
    refine ⟨64708147083110425500502997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43138764722073617000335331 64708147083110425500502997)
    ·
      refine ⟨1516597197260400597668039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 64708147083110425500502997 1516597197260400597668039)
      ·
        refine ⟨2274895795890600896502059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516597197260400597668039 2274895795890600896502059)
        ·
          refine ⟨3412343693835901344753089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274895795890600896502059 3412343693835901344753089)
          ·
            refine ⟨2559257770376926008564817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412343693835901344753089 2559257770376926008564817)
            ·
              refine ⟨1919443327782694506423613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559257770376926008564817 1919443327782694506423613)
              ·
                refine ⟨719791247918510439908855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1919443327782694506423613 719791247918510439908855)
                ·
                  refine ⟨1079686871877765659863283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719791247918510439908855 1079686871877765659863283)
                  ·
                    refine ⟨1619530307816648489794925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079686871877765659863283 1619530307816648489794925)
                    ·
                      refine ⟨607323865431243183673097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619530307816648489794925 607323865431243183673097)
                      ·
                        rfl

theorem cell23_1182759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1182759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182759 prefixEnd_1182759 := by exact prefixLift 1182759
  have htrace : WordTrace (prefixWord ++ tailWord_1182759) baseStart_1182759 baseEnd_1182759 := by
    simpa [prefixWord, tailWord_1182759, baseEnd_1182759] using wordTrace_append hprefix tailTrace_1182759
  have hstable : (prefixWord ++ tailWord_1182759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182759).length < 2 ^ (prefixWord ++ tailWord_1182759).sum := by decide
  have hdescent : baseEnd_1182759 < baseStart_1182759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182762 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1182762 : Nat := 118140960795 + 1182762 * 2 ^ 59
def prefixEnd_1182762 : Nat := 4983230072969 + 3 ^ 40 * 1182762 * 2
def baseEnd_1182762 : Nat := 202441801957735557311861

theorem tailTrace_1182762 : CollatzResearch.WordTrace tailWord_1182762 prefixEnd_1182762 202441801957735557311861 := by
  unfold tailWord_1182762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10784718535265687128173635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28759249427375165675129693 10784718535265687128173635)
  ·
    refine ⟨16177077802898530692260453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10784718535265687128173635 16177077802898530692260453)
    ·
      refine ⟨3033202088043474504798835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16177077802898530692260453 3033202088043474504798835)
      ·
        refine ⟨4549803132065211757198253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033202088043474504798835 4549803132065211757198253)
        ·
          refine ⟨1706176174524454408949345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4549803132065211757198253 1706176174524454408949345)
          ·
            refine ⟨1279632130893340806712009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706176174524454408949345 1279632130893340806712009)
            ·
              refine ⟨959724098170005605034007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279632130893340806712009 959724098170005605034007)
              ·
                refine ⟨1439586147255008407551011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959724098170005605034007 1439586147255008407551011)
                ·
                  refine ⟨2159379220882512611326517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439586147255008407551011 2159379220882512611326517)
                  ·
                    refine ⟨202441801957735557311861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2159379220882512611326517 202441801957735557311861)
                    ·
                      rfl

theorem cell23_1182762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1182762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182762 prefixEnd_1182762 := by exact prefixLift 1182762
  have htrace : WordTrace (prefixWord ++ tailWord_1182762) baseStart_1182762 baseEnd_1182762 := by
    simpa [prefixWord, tailWord_1182762, baseEnd_1182762] using wordTrace_append hprefix tailTrace_1182762
  have hstable : (prefixWord ++ tailWord_1182762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182762).length < 2 ^ (prefixWord ++ tailWord_1182762).sum := by decide
  have hdescent : baseEnd_1182762 < baseStart_1182762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182768 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_1182768 : Nat := 118140960795 + 1182768 * 2 ^ 59
def prefixEnd_1182768 : Nat := 4983230072969 + 3 ^ 40 * 1182768 * 2
def baseEnd_1182768 : Nat := 607328486757133648460555

theorem tailTrace_1182768 : CollatzResearch.WordTrace tailWord_1182768 prefixEnd_1182768 607328486757133648460555 := by
  unfold tailWord_1182768
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569546489520505768706479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28759395319360674358275305 21569546489520505768706479)
  ·
    refine ⟨32354319734280758653059719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21569546489520505768706479 32354319734280758653059719)
    ·
      refine ⟨48531479601421137979589579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32354319734280758653059719 48531479601421137979589579)
      ·
        refine ⟨72797219402131706969384369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48531479601421137979589579 72797219402131706969384369)
        ·
          refine ⟨54597914551598780227038277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72797219402131706969384369 54597914551598780227038277)
          ·
            refine ⟨10237108978424771292569677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54597914551598780227038277 10237108978424771292569677)
            ·
              refine ⟨3838915866909289234713629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10237108978424771292569677 3838915866909289234713629)
              ·
                refine ⟨1439593450090983463017611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3838915866909289234713629 1439593450090983463017611)
                ·
                  refine ⟨2159390175136475194526417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439593450090983463017611 2159390175136475194526417)
                  ·
                    refine ⟨1619542631352356395894813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2159390175136475194526417 1619542631352356395894813)
                    ·
                      refine ⟨607328486757133648460555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619542631352356395894813 607328486757133648460555)
                      ·
                        rfl

theorem cell23_1182768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_1182768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182768 prefixEnd_1182768 := by exact prefixLift 1182768
  have htrace : WordTrace (prefixWord ++ tailWord_1182768) baseStart_1182768 baseEnd_1182768 := by
    simpa [prefixWord, tailWord_1182768, baseEnd_1182768] using wordTrace_append hprefix tailTrace_1182768
  have hstable : (prefixWord ++ tailWord_1182768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182768).length < 2 ^ (prefixWord ++ tailWord_1182768).sum := by decide
  have hdescent : baseEnd_1182768 < baseStart_1182768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182782 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1182782 : Nat := 118140960795 + 1182782 * 2 ^ 59
def prefixEnd_1182782 : Nat := 4983230072969 + 3 ^ 40 * 1182782 * 2
def baseEnd_1182782 : Nat := 607335675486296593685491

theorem tailTrace_1182782 : CollatzResearch.WordTrace tailWord_1182782 prefixEnd_1182782 607335675486296593685491 := by
  unfold tailWord_1182782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392450450123786491052825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28759735733993527952281733 5392450450123786491052825)
  ·
    refine ⟨4044337837592839868289619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5392450450123786491052825 4044337837592839868289619)
    ·
      refine ⟨6066506756389259802434429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044337837592839868289619 6066506756389259802434429)
      ·
        refine ⟨2274940033645972425912911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6066506756389259802434429 2274940033645972425912911)
        ·
          refine ⟨3412410050468958638869367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274940033645972425912911 3412410050468958638869367)
          ·
            refine ⟨5118615075703437958304051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412410050468958638869367 5118615075703437958304051)
            ·
              refine ⟨7677922613555156937456077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118615075703437958304051 7677922613555156937456077)
              ·
                refine ⟨2879220980083183851546029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7677922613555156937456077 2879220980083183851546029)
                ·
                  refine ⟨1079707867531193944329761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2879220980083183851546029 1079707867531193944329761)
                  ·
                    refine ⟨809780900648395458247321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1079707867531193944329761 809780900648395458247321)
                    ·
                      refine ⟨607335675486296593685491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809780900648395458247321 607335675486296593685491)
                      ·
                        rfl

theorem cell23_1182782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1182782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182782 prefixEnd_1182782 := by exact prefixLift 1182782
  have htrace : WordTrace (prefixWord ++ tailWord_1182782) baseStart_1182782 baseEnd_1182782 := by
    simpa [prefixWord, tailWord_1182782, baseEnd_1182782] using wordTrace_append hprefix tailTrace_1182782
  have hstable : (prefixWord ++ tailWord_1182782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182782).length < 2 ^ (prefixWord ++ tailWord_1182782).sum := by decide
  have hdescent : baseEnd_1182782 < baseStart_1182782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182825 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 1, 3, 2]
def baseStart_1182825 : Nat := 118140960795 + 1182825 * 2 ^ 59
def prefixEnd_1182825 : Nat := 4983230072969 + 3 ^ 40 * 1182825 * 2
def baseEnd_1182825 : Nat := 607357755154439925447793

theorem tailTrace_1182825 : CollatzResearch.WordTrace tailWord_1182825 prefixEnd_1182825 607357755154439925447793 := by
  unfold tailWord_1182825
  simp only [CollatzResearch.WordTrace]
  refine ⟨43141171939834510272237929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28760781293223006848158619 43141171939834510272237929)
  ·
    refine ⟨32355878954875882704178447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43141171939834510272237929 32355878954875882704178447)
    ·
      refine ⟨48533818432313824056267671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32355878954875882704178447 48533818432313824056267671)
      ·
        refine ⟨72800727648470736084401507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48533818432313824056267671 72800727648470736084401507)
        ·
          refine ⟨109201091472706104126602261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72800727648470736084401507 109201091472706104126602261)
          ·
            refine ⟨5118801162783098630934481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109201091472706104126602261 5118801162783098630934481)
            ·
              refine ⟨3839100872087323973200861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118801162783098630934481 3839100872087323973200861)
              ·
                refine ⟨1439662827032746489950323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3839100872087323973200861 1439662827032746489950323)
                ·
                  refine ⟨2159494240549119734925485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439662827032746489950323 2159494240549119734925485)
                  ·
                    refine ⟨809810340205919900597057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2159494240549119734925485 809810340205919900597057)
                    ·
                      refine ⟨607357755154439925447793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809810340205919900597057 607357755154439925447793)
                      ·
                        rfl

theorem cell23_1182825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3, 2].length) (baseStart_1182825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182825 prefixEnd_1182825 := by exact prefixLift 1182825
  have htrace : WordTrace (prefixWord ++ tailWord_1182825) baseStart_1182825 baseEnd_1182825 := by
    simpa [prefixWord, tailWord_1182825, baseEnd_1182825] using wordTrace_append hprefix tailTrace_1182825
  have hstable : (prefixWord ++ tailWord_1182825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182825).length < 2 ^ (prefixWord ++ tailWord_1182825).sum := by decide
  have hdescent : baseEnd_1182825 < baseStart_1182825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182838 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1182838 : Nat := 118140960795 + 1182838 * 2 ^ 59
def prefixEnd_1182838 : Nat := 4983230072969 + 3 ^ 40 * 1182838 * 2
def baseEnd_1182838 : Nat := 607364430402948374585233

theorem tailTrace_1182838 : CollatzResearch.WordTrace tailWord_1182838 prefixEnd_1182838 607364430402948374585233 := by
  unfold tailWord_1182838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696352880549213343278823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28761097392524942328307445 2696352880549213343278823)
  ·
    refine ⟨4044529320823820014918235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696352880549213343278823 4044529320823820014918235)
    ·
      refine ⟨6066793981235730022377353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044529320823820014918235 6066793981235730022377353)
      ·
        refine ⟨4550095485926797516783015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066793981235730022377353 4550095485926797516783015)
        ·
          refine ⟨6825143228890196275174523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550095485926797516783015 6825143228890196275174523)
          ·
            refine ⟨10237714843335294412761785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825143228890196275174523 10237714843335294412761785)
            ·
              refine ⟨7678286132501470809571339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10237714843335294412761785 7678286132501470809571339)
              ·
                refine ⟨11517429198752206214357009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678286132501470809571339 11517429198752206214357009)
                ·
                  refine ⟨8638071899064154660767757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11517429198752206214357009 8638071899064154660767757)
                  ·
                    refine ⟨3239276962149057997787909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8638071899064154660767757 3239276962149057997787909)
                    ·
                      refine ⟨607364430402948374585233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3239276962149057997787909 607364430402948374585233)
                      ·
                        rfl

theorem cell23_1182838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1182838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182838 prefixEnd_1182838 := by exact prefixLift 1182838
  have htrace : WordTrace (prefixWord ++ tailWord_1182838) baseStart_1182838 baseEnd_1182838 := by
    simpa [prefixWord, tailWord_1182838, baseEnd_1182838] using wordTrace_append hprefix tailTrace_1182838
  have hstable : (prefixWord ++ tailWord_1182838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182838).length < 2 ^ (prefixWord ++ tailWord_1182838).sum := by decide
  have hdescent : baseEnd_1182838 < baseStart_1182838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182849 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_1182849 : Nat := 118140960795 + 1182849 * 2 ^ 59
def prefixEnd_1182849 : Nat := 4983230072969 + 3 ^ 40 * 1182849 * 2
def baseEnd_1182849 : Nat := 607370078690147831547683

theorem tailTrace_1182849 : CollatzResearch.WordTrace tailWord_1182849 prefixEnd_1182849 607370078690147831547683 := by
  unfold tailWord_1182849
  simp only [CollatzResearch.WordTrace]
  refine ⟨43142047291747562371111601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28761364861165041580741067 43142047291747562371111601)
  ·
    refine ⟨32356535468810671778333701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43142047291747562371111601 32356535468810671778333701)
    ·
      refine ⟨6066850400402000958437569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32356535468810671778333701 6066850400402000958437569)
      ·
        refine ⟨4550137800301500718828177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066850400402000958437569 4550137800301500718828177)
        ·
          refine ⟨3412603350226125539121133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4550137800301500718828177 3412603350226125539121133)
          ·
            refine ⟨1279726256334797077170425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3412603350226125539121133 1279726256334797077170425)
            ·
              refine ⟨959794692251097807877819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279726256334797077170425 959794692251097807877819)
              ·
                refine ⟨1439692038376646711816729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959794692251097807877819 1439692038376646711816729)
                ·
                  refine ⟨1079769028782485033862547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1439692038376646711816729 1079769028782485033862547)
                  ·
                    refine ⟨1619653543173727550793821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1079769028782485033862547 1619653543173727550793821)
                    ·
                      refine ⟨607370078690147831547683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1619653543173727550793821 607370078690147831547683)
                      ·
                        rfl

theorem cell23_1182849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_1182849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182849 prefixEnd_1182849 := by exact prefixLift 1182849
  have htrace : WordTrace (prefixWord ++ tailWord_1182849) baseStart_1182849 baseEnd_1182849 := by
    simpa [prefixWord, tailWord_1182849, baseEnd_1182849] using wordTrace_append hprefix tailTrace_1182849
  have hstable : (prefixWord ++ tailWord_1182849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182849).length < 2 ^ (prefixWord ++ tailWord_1182849).sum := by decide
  have hdescent : baseEnd_1182849 < baseStart_1182849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182851 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1182851 : Nat := 118140960795 + 1182851 * 2 ^ 59
def prefixEnd_1182851 : Nat := 4983230072969 + 3 ^ 40 * 1182851 * 2
def baseEnd_1182851 : Nat := 607371105651456823722673

theorem tailTrace_1182851 : CollatzResearch.WordTrace tailWord_1182851 prefixEnd_1182851 607371105651456823722673 := by
  unfold tailWord_1182851
  simp only [CollatzResearch.WordTrace]
  refine ⟨43142120237740316712684407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28761413491826877808456271 43142120237740316712684407)
  ·
    refine ⟨64713180356610475069026611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43142120237740316712684407 64713180356610475069026611)
    ·
      refine ⟨97069770534915712603539917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64713180356610475069026611 97069770534915712603539917)
      ·
        refine ⟨36401163950593392226327469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97069770534915712603539917 36401163950593392226327469)
        ·
          refine ⟨13650436481472522084872801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36401163950593392226327469 13650436481472522084872801)
          ·
            refine ⟨10237827361104391563654601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13650436481472522084872801 10237827361104391563654601)
            ·
              refine ⟨7678370520828293672740951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10237827361104391563654601 7678370520828293672740951)
              ·
                refine ⟨11517555781242440509111427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678370520828293672740951 11517555781242440509111427)
                ·
                  refine ⟨17276333671863660763667141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11517555781242440509111427 17276333671863660763667141)
                  ·
                    refine ⟨3239312563474436393187589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17276333671863660763667141 3239312563474436393187589)
                    ·
                      refine ⟨607371105651456823722673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3239312563474436393187589 607371105651456823722673)
                      ·
                        rfl

theorem cell23_1182851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1182851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182851 prefixEnd_1182851 := by exact prefixLift 1182851
  have htrace : WordTrace (prefixWord ++ tailWord_1182851) baseStart_1182851 baseEnd_1182851 := by
    simpa [prefixWord, tailWord_1182851, baseEnd_1182851] using wordTrace_append hprefix tailTrace_1182851
  have hstable : (prefixWord ++ tailWord_1182851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182851).length < 2 ^ (prefixWord ++ tailWord_1182851).sum := by decide
  have hdescent : baseEnd_1182851 < baseStart_1182851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182895 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 5]
def baseStart_1182895 : Nat := 118140960795 + 1182895 * 2 ^ 59
def prefixEnd_1182895 : Nat := 4983230072969 + 3 ^ 40 * 1182895 * 2
def baseEnd_1182895 : Nat := 67488188755583850174719

theorem tailTrace_1182895 : CollatzResearch.WordTrace tailWord_1182895 prefixEnd_1182895 67488188755583850174719 := by
  unfold tailWord_1182895
  simp only [CollatzResearch.WordTrace]
  refine ⟨43143725049580912227286139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28762483366387274818190759 43143725049580912227286139)
  ·
    refine ⟨64715587574371368340929209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43143725049580912227286139 64715587574371368340929209)
    ·
      refine ⟨48536690680778526255696907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64715587574371368340929209 48536690680778526255696907)
      ·
        refine ⟨72805036021167789383545361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48536690680778526255696907 72805036021167789383545361)
        ·
          refine ⟨54603777015875842037659021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72805036021167789383545361 54603777015875842037659021)
          ·
            refine ⟨20476416380953440764122133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54603777015875842037659021 20476416380953440764122133)
            ·
              refine ⟨959832017857192535818225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20476416380953440764122133 959832017857192535818225)
              ·
                refine ⟨719874013392894401863669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959832017857192535818225 719874013392894401863669)
                ·
                  refine ⟨67488188755583850174719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 719874013392894401863669 67488188755583850174719)
                  ·
                    rfl

theorem cell23_1182895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 5].length) (baseStart_1182895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182895 prefixEnd_1182895 := by exact prefixLift 1182895
  have htrace : WordTrace (prefixWord ++ tailWord_1182895) baseStart_1182895 baseEnd_1182895 := by
    simpa [prefixWord, tailWord_1182895, baseEnd_1182895] using wordTrace_append hprefix tailTrace_1182895
  have hstable : (prefixWord ++ tailWord_1182895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182895).length < 2 ^ (prefixWord ++ tailWord_1182895).sum := by decide
  have hdescent : baseEnd_1182895 < baseStart_1182895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182938 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_1182938 : Nat := 118140960795 + 1182938 * 2 ^ 59
def prefixEnd_1182938 : Nat := 4983230072969 + 3 ^ 40 * 1182938 * 2
def baseEnd_1182938 : Nat := 202471926156132661111591

theorem tailTrace_1182938 : CollatzResearch.WordTrace tailWord_1182938 prefixEnd_1182938 202471926156132661111591 := by
  unfold tailWord_1182938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786323347106282642775367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28763528925616753714067645 10786323347106282642775367)
  ·
    refine ⟨16179485020659423964163051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10786323347106282642775367 16179485020659423964163051)
    ·
      refine ⟨24269227530989135946244577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16179485020659423964163051 24269227530989135946244577)
      ·
        refine ⟨18201920648241851959683433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24269227530989135946244577 18201920648241851959683433)
        ·
          refine ⟨13651440486181388969762575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18201920648241851959683433 13651440486181388969762575)
          ·
            refine ⟨20477160729272083454643863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651440486181388969762575 20477160729272083454643863)
            ·
              refine ⟨30715741093908125181965795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20477160729272083454643863 30715741093908125181965795)
              ·
                refine ⟨46073611640862187772948693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30715741093908125181965795 46073611640862187772948693)
                ·
                  refine ⟨1079850272832707525928485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46073611640862187772948693 1079850272832707525928485)
                  ·
                    refine ⟨202471926156132661111591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079850272832707525928485 202471926156132661111591)
                    ·
                      rfl

theorem cell23_1182938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_1182938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182938 prefixEnd_1182938 := by exact prefixLift 1182938
  have htrace : WordTrace (prefixWord ++ tailWord_1182938) baseStart_1182938 baseEnd_1182938 := by
    simpa [prefixWord, tailWord_1182938, baseEnd_1182938] using wordTrace_append hprefix tailTrace_1182938
  have hstable : (prefixWord ++ tailWord_1182938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182938).length < 2 ^ (prefixWord ++ tailWord_1182938).sum := by decide
  have hdescent : baseEnd_1182938 < baseStart_1182938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182945 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_1182945 : Nat := 118140960795 + 1182945 * 2 ^ 59
def prefixEnd_1182945 : Nat := 4983230072969 + 3 ^ 40 * 1182945 * 2
def baseEnd_1182945 : Nat := 607419372832979455947241

theorem tailTrace_1182945 : CollatzResearch.WordTrace tailWord_1182945 prefixEnd_1182945 607419372832979455947241 := by
  unfold tailWord_1182945
  simp only [CollatzResearch.WordTrace]
  refine ⟨43145548699399770766606289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28763699132933180511070859 43145548699399770766606289)
  ·
    refine ⟨32359161524549828074954717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43145548699399770766606289 32359161524549828074954717)
    ·
      refine ⟨12134685571706185528108019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32359161524549828074954717 12134685571706185528108019)
      ·
        refine ⟨18202028357559278292162029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12134685571706185528108019 18202028357559278292162029)
        ·
          refine ⟨6825760634084729359560761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18202028357559278292162029 6825760634084729359560761)
          ·
            refine ⟨5119320475563547019670571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6825760634084729359560761 5119320475563547019670571)
            ·
              refine ⟨7678980713345320529505857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119320475563547019670571 7678980713345320529505857)
              ·
                refine ⟨5759235535008990397129393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7678980713345320529505857 5759235535008990397129393)
                ·
                  refine ⟨4319426651256742797847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759235535008990397129393 4319426651256742797847045)
                  ·
                    refine ⟨809892497110639274596321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319426651256742797847045 809892497110639274596321)
                    ·
                      refine ⟨607419372832979455947241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 809892497110639274596321 607419372832979455947241)
                      ·
                        rfl

theorem cell23_1182945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_1182945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182945 prefixEnd_1182945 := by exact prefixLift 1182945
  have htrace : WordTrace (prefixWord ++ tailWord_1182945) baseStart_1182945 baseEnd_1182945 := by
    simpa [prefixWord, tailWord_1182945, baseEnd_1182945] using wordTrace_append hprefix tailTrace_1182945
  have hstable : (prefixWord ++ tailWord_1182945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182945).length < 2 ^ (prefixWord ++ tailWord_1182945).sum := by decide
  have hdescent : baseEnd_1182945 < baseStart_1182945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182955 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 3, 4]
def baseStart_1182955 : Nat := 118140960795 + 1182955 * 2 ^ 59
def prefixEnd_1182955 : Nat := 4983230072969 + 3 ^ 40 * 1182955 * 2
def baseEnd_1182955 : Nat := 202474835879841472274065

theorem tailTrace_1182955 : CollatzResearch.WordTrace tailWord_1182955 prefixEnd_1182955 202474835879841472274065 := by
  unfold tailWord_1182955
  simp only [CollatzResearch.WordTrace]
  refine ⟨43145913429363542474470319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28763942286242361649646879 43145913429363542474470319)
  ·
    refine ⟨64718870144045313711705479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43145913429363542474470319 64718870144045313711705479)
    ·
      refine ⟨97078305216067970567558219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64718870144045313711705479 97078305216067970567558219)
      ·
        refine ⟨145617457824101955851337329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97078305216067970567558219 145617457824101955851337329)
        ·
          refine ⟨109213093368076466888502997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145617457824101955851337329 109213093368076466888502997)
          ·
            refine ⟨2559681875814292192699289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109213093368076466888502997 2559681875814292192699289)
            ·
              refine ⟨1919761406860719144524467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559681875814292192699289 1919761406860719144524467)
              ·
                refine ⟨2879642110291078716786701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919761406860719144524467 2879642110291078716786701)
                ·
                  refine ⟨1079865791359154518795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2879642110291078716786701 1079865791359154518795013)
                  ·
                    refine ⟨202474835879841472274065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079865791359154518795013 202474835879841472274065)
                    ·
                      rfl

theorem cell23_1182955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 4].length) (baseStart_1182955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1182955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1182955 prefixEnd_1182955 := by exact prefixLift 1182955
  have htrace : WordTrace (prefixWord ++ tailWord_1182955) baseStart_1182955 baseEnd_1182955 := by
    simpa [prefixWord, tailWord_1182955, baseEnd_1182955] using wordTrace_append hprefix tailTrace_1182955
  have hstable : (prefixWord ++ tailWord_1182955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182955).length < 2 ^ (prefixWord ++ tailWord_1182955).sum := by decide
  have hdescent : baseEnd_1182955 < baseStart_1182955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183006 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1183006 : Nat := 118140960795 + 1183006 * 2 ^ 59
def prefixEnd_1183006 : Nat := 4983230072969 + 3 ^ 40 * 1183006 * 2
def baseEnd_1183006 : Nat := 202483565050967905761487

theorem tailTrace_1183006 : CollatzResearch.WordTrace tailWord_1183006 prefixEnd_1183006 202483565050967905761487 := by
  unfold tailWord_1183006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393471694022347273072109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28765182368119185456384581 5393471694022347273072109)
  ·
    refine ⟨2022551885258380227402041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5393471694022347273072109 2022551885258380227402041)
    ·
      refine ⟨1516913913943785170551531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2022551885258380227402041 1516913913943785170551531)
      ·
        refine ⟨2275370870915677755827297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516913913943785170551531 2275370870915677755827297)
        ·
          refine ⟨1706528153186758316870473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275370870915677755827297 1706528153186758316870473)
          ·
            refine ⟨1279896114890068737652855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706528153186758316870473 1279896114890068737652855)
            ·
              refine ⟨1919844172335103106479283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279896114890068737652855 1919844172335103106479283)
              ·
                refine ⟨2879766258502654659718925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919844172335103106479283 2879766258502654659718925)
                ·
                  refine ⟨1079912346938495497394597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2879766258502654659718925 1079912346938495497394597)
                  ·
                    refine ⟨202483565050967905761487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079912346938495497394597 202483565050967905761487)
                    ·
                      rfl

theorem cell23_1183006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1183006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183006 prefixEnd_1183006 := by exact prefixLift 1183006
  have htrace : WordTrace (prefixWord ++ tailWord_1183006) baseStart_1183006 baseEnd_1183006 := by
    simpa [prefixWord, tailWord_1183006, baseEnd_1183006] using wordTrace_append hprefix tailTrace_1183006
  have hstable : (prefixWord ++ tailWord_1183006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183006).length < 2 ^ (prefixWord ++ tailWord_1183006).sum := by decide
  have hdescent : baseEnd_1183006 < baseStart_1183006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183075 : List Nat := [1, 1, 1, 5, 2, 4, 1, 8]
def baseStart_1183075 : Nat := 118140960795 + 1183075 * 2 ^ 59
def prefixEnd_1183075 : Nat := 4983230072969 + 3 ^ 40 * 1183075 * 2
def baseEnd_1183075 : Nat := 22499486122891257308209

theorem tailTrace_1183075 : CollatzResearch.WordTrace tailWord_1183075 prefixEnd_1183075 22499486122891257308209 := by
  unfold tailWord_1183075
  simp only [CollatzResearch.WordTrace]
  refine ⟨43150290188928802968838679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28766860125952535312559119 43150290188928802968838679)
  ·
    refine ⟨64725435283393204453258019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43150290188928802968838679 64725435283393204453258019)
    ·
      refine ⟨97088152925089806679887029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64725435283393204453258019 97088152925089806679887029)
      ·
        refine ⟨9102014336727169376239409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97088152925089806679887029 9102014336727169376239409)
        ·
          refine ⟨6826510752545377032179557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9102014336727169376239409 6826510752545377032179557)
          ·
            refine ⟨1279970766102258193533667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6826510752545377032179557 1279970766102258193533667)
            ·
              refine ⟨1919956149153387290300501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279970766102258193533667 1919956149153387290300501)
              ·
                refine ⟨22499486122891257308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1919956149153387290300501 22499486122891257308209)
                ·
                  rfl

theorem cell23_1183075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 8].length) (baseStart_1183075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183075 prefixEnd_1183075 := by exact prefixLift 1183075
  have htrace : WordTrace (prefixWord ++ tailWord_1183075) baseStart_1183075 baseEnd_1183075 := by
    simpa [prefixWord, tailWord_1183075, baseEnd_1183075] using wordTrace_append hprefix tailTrace_1183075
  have hstable : (prefixWord ++ tailWord_1183075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183075).length < 2 ^ (prefixWord ++ tailWord_1183075).sum := by decide
  have hdescent : baseEnd_1183075 < baseStart_1183075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183088 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_1183088 : Nat := 118140960795 + 1183088 * 2 ^ 59
def prefixEnd_1183088 : Nat := 4983230072969 + 3 ^ 40 * 1183088 * 2
def baseEnd_1183088 : Nat := 202497600188857465486361

theorem tailTrace_1183088 : CollatzResearch.WordTrace tailWord_1183088 prefixEnd_1183088 202497600188857465486361 := by
  unfold tailWord_1183088
  simp only [CollatzResearch.WordTrace]
  refine ⟨21575382168940853094530959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28767176225254470792707945 21575382168940853094530959)
  ·
    refine ⟨32363073253411279641796439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21575382168940853094530959 32363073253411279641796439)
    ·
      refine ⟨48544609880116919462694659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32363073253411279641796439 48544609880116919462694659)
      ·
        refine ⟨72816914820175379194041989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48544609880116919462694659 72816914820175379194041989)
        ·
          refine ⟨13653171528782883598882873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72816914820175379194041989 13653171528782883598882873)
          ·
            refine ⟨10239878646587162699162155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13653171528782883598882873 10239878646587162699162155)
            ·
              refine ⟨15359817969880744048743233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239878646587162699162155 15359817969880744048743233)
              ·
                refine ⟨11519863477410558036557425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15359817969880744048743233 11519863477410558036557425)
                ·
                  refine ⟨8639897608057918527418069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519863477410558036557425 8639897608057918527418069)
                  ·
                    refine ⟨202497600188857465486361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8639897608057918527418069 202497600188857465486361)
                    ·
                      rfl

theorem cell23_1183088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_1183088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183088 prefixEnd_1183088 := by exact prefixLift 1183088
  have htrace : WordTrace (prefixWord ++ tailWord_1183088) baseStart_1183088 baseEnd_1183088 := by
    simpa [prefixWord, tailWord_1183088, baseEnd_1183088] using wordTrace_append hprefix tailTrace_1183088
  have hstable : (prefixWord ++ tailWord_1183088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183088).length < 2 ^ (prefixWord ++ tailWord_1183088).sum := by decide
  have hdescent : baseEnd_1183088 < baseStart_1183088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183098 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1183098 : Nat := 118140960795 + 1183098 * 2 ^ 59
def prefixEnd_1183098 : Nat := 4983230072969 + 3 ^ 40 * 1183098 * 2
def baseEnd_1183098 : Nat := 607497935373117357334037

theorem tailTrace_1183098 : CollatzResearch.WordTrace tailWord_1183098 prefixEnd_1183098 607497935373117357334037 := by
  unfold tailWord_1183098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787782266961369474231487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28767419378563651931283965 10787782266961369474231487)
  ·
    refine ⟨16181673400442054211347231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10787782266961369474231487 16181673400442054211347231)
    ·
      refine ⟨24272510100663081317020847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16181673400442054211347231 24272510100663081317020847)
      ·
        refine ⟨36408765150994621975531271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24272510100663081317020847 36408765150994621975531271)
        ·
          refine ⟨54613147726491932963296907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36408765150994621975531271 54613147726491932963296907)
          ·
            refine ⟨81919721589737899444945361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54613147726491932963296907 81919721589737899444945361)
            ·
              refine ⟨61439791192303424583709021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81919721589737899444945361 61439791192303424583709021)
              ·
                refine ⟨23039921697113784218890883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61439791192303424583709021 23039921697113784218890883)
                ·
                  refine ⟨34559882545670676328336325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23039921697113784218890883 34559882545670676328336325)
                  ·
                    refine ⟨6479977977313251811563061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34559882545670676328336325 6479977977313251811563061)
                    ·
                      refine ⟨607497935373117357334037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6479977977313251811563061 607497935373117357334037)
                      ·
                        rfl

theorem cell23_1183098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1183098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183098 prefixEnd_1183098 := by exact prefixLift 1183098
  have htrace : WordTrace (prefixWord ++ tailWord_1183098) baseStart_1183098 baseEnd_1183098 := by
    simpa [prefixWord, tailWord_1183098, baseEnd_1183098] using wordTrace_append hprefix tailTrace_1183098
  have hstable : (prefixWord ++ tailWord_1183098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183098).length < 2 ^ (prefixWord ++ tailWord_1183098).sum := by decide
  have hdescent : baseEnd_1183098 < baseStart_1183098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183106 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1183106 : Nat := 118140960795 + 1183106 * 2 ^ 59
def prefixEnd_1183106 : Nat := 4983230072969 + 3 ^ 40 * 1183106 * 2
def baseEnd_1183106 : Nat := 607502043218353326034001

theorem tailTrace_1183106 : CollatzResearch.WordTrace tailWord_1183106 prefixEnd_1183106 607502043218353326034001 := by
  unfold tailWord_1183106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787855212954123815804293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28767613901210996842144781 10787855212954123815804293)
  ·
    refine ⟨2022722852428898215463305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10787855212954123815804293 2022722852428898215463305)
    ·
      refine ⟨1517042139321673661597479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2022722852428898215463305 1517042139321673661597479)
      ·
        refine ⟨2275563208982510492396219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517042139321673661597479 2275563208982510492396219)
        ·
          refine ⟨3413344813473765738594329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275563208982510492396219 3413344813473765738594329)
          ·
            refine ⟨2560008610105324303945747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413344813473765738594329 2560008610105324303945747)
            ·
              refine ⟨3840012915157986455918621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560008610105324303945747 3840012915157986455918621)
              ·
                refine ⟨1440004843184244920969483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3840012915157986455918621 1440004843184244920969483)
                ·
                  refine ⟨2160007264776367381454225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440004843184244920969483 2160007264776367381454225)
                  ·
                    refine ⟨1620005448582275536090669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160007264776367381454225 1620005448582275536090669)
                    ·
                      refine ⟨607502043218353326034001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620005448582275536090669 607502043218353326034001)
                      ·
                        rfl

theorem cell23_1183106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1183106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183106 prefixEnd_1183106 := by exact prefixLift 1183106
  have htrace : WordTrace (prefixWord ++ tailWord_1183106) baseStart_1183106 baseEnd_1183106 := by
    simpa [prefixWord, tailWord_1183106, baseEnd_1183106] using wordTrace_append hprefix tailTrace_1183106
  have hstable : (prefixWord ++ tailWord_1183106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183106).length < 2 ^ (prefixWord ++ tailWord_1183106).sum := by decide
  have hdescent : baseEnd_1183106 < baseStart_1183106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183135 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 2, 6]
def baseStart_1183135 : Nat := 118140960795 + 1183135 * 2 ^ 59
def prefixEnd_1183135 : Nat := 4983230072969 + 3 ^ 40 * 1183135 * 2
def baseEnd_1183135 : Nat := 202505644719111237523789

theorem tailTrace_1183135 : CollatzResearch.WordTrace tailWord_1183135 prefixEnd_1183135 202505644719111237523789 := by
  unfold tailWord_1183135
  simp only [CollatzResearch.WordTrace]
  refine ⟨43152478568711433216022859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28768319045807622144015239 43152478568711433216022859)
  ·
    refine ⟨64728717853067149824034289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43152478568711433216022859 64728717853067149824034289)
    ·
      refine ⟨48546538389800362368025717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64728717853067149824034289 48546538389800362368025717)
      ·
        refine ⟨4551237974043783972002411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48546538389800362368025717 4551237974043783972002411)
        ·
          refine ⟨6826856961065675958003617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551237974043783972002411 6826856961065675958003617)
          ·
            refine ⟨5120142720799256968502713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6826856961065675958003617 5120142720799256968502713)
            ·
              refine ⟨3840107040599442726377035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120142720799256968502713 3840107040599442726377035)
              ·
                refine ⟨5760160560899164089565553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840107040599442726377035 5760160560899164089565553)
                ·
                  refine ⟨4320120420674373067174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760160560899164089565553 4320120420674373067174165)
                  ·
                    refine ⟨202505644719111237523789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4320120420674373067174165 202505644719111237523789)
                    ·
                      rfl

theorem cell23_1183135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_1183135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183135 prefixEnd_1183135 := by exact prefixLift 1183135
  have htrace : WordTrace (prefixWord ++ tailWord_1183135) baseStart_1183135 baseEnd_1183135 := by
    simpa [prefixWord, tailWord_1183135, baseEnd_1183135] using wordTrace_append hprefix tailTrace_1183135
  have hstable : (prefixWord ++ tailWord_1183135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183135).length < 2 ^ (prefixWord ++ tailWord_1183135).sum := by decide
  have hdescent : baseEnd_1183135 < baseStart_1183135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183182 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_1183182 : Nat := 118140960795 + 1183182 * 2 ^ 59
def prefixEnd_1183182 : Nat := 4983230072969 + 3 ^ 40 * 1183182 * 2
def baseEnd_1183182 : Nat := 67504563083121669853739

theorem tailTrace_1183182 : CollatzResearch.WordTrace tailWord_1183182 prefixEnd_1183182 67504563083121669853739 := by
  unfold tailWord_1183182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394274099942645030372975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28769461866360773495322533 5394274099942645030372975)
  ·
    refine ⟨8091411149913967545559463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5394274099942645030372975 8091411149913967545559463)
    ·
      refine ⟨12137116724870951318339195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8091411149913967545559463 12137116724870951318339195)
      ·
        refine ⟨18205675087306426977508793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12137116724870951318339195 18205675087306426977508793)
        ·
          refine ⟨13654256315479820233131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18205675087306426977508793 13654256315479820233131595)
          ·
            refine ⟨20481384473219730349697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13654256315479820233131595 20481384473219730349697393)
            ·
              refine ⟨15361038354914797762273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20481384473219730349697393 15361038354914797762273045)
              ·
                refine ⟨720048672886631145106549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15361038354914797762273045 720048672886631145106549)
                ·
                  refine ⟨67504563083121669853739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720048672886631145106549 67504563083121669853739)
                  ·
                    rfl

theorem cell23_1183182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_1183182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183182 prefixEnd_1183182 := by exact prefixLift 1183182
  have htrace : WordTrace (prefixWord ++ tailWord_1183182) baseStart_1183182 baseEnd_1183182 := by
    simpa [prefixWord, tailWord_1183182, baseEnd_1183182] using wordTrace_append hprefix tailTrace_1183182
  have hstable : (prefixWord ++ tailWord_1183182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183182).length < 2 ^ (prefixWord ++ tailWord_1183182).sum := by decide
  have hdescent : baseEnd_1183182 < baseStart_1183182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183193 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 2, 2, 2]
def baseStart_1183193 : Nat := 118140960795 + 1183193 * 2 ^ 59
def prefixEnd_1183193 : Nat := 4983230072969 + 3 ^ 40 * 1183193 * 2
def baseEnd_1183193 : Nat := 607546716035294485646101

theorem tailTrace_1183193 : CollatzResearch.WordTrace tailWord_1183193 prefixEnd_1183193 607546716035294485646101 := by
  unfold tailWord_1183193
  simp only [CollatzResearch.WordTrace]
  refine ⟨43154594002501309121634233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28769729335000872747756155 43154594002501309121634233)
  ·
    refine ⟨32365945501875981841225675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43154594002501309121634233 32365945501875981841225675)
    ·
      refine ⟨48548918252813972761838513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32365945501875981841225675 48548918252813972761838513)
      ·
        refine ⟨36411688689610479571378885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48548918252813972761838513 36411688689610479571378885)
        ·
          refine ⟨6827191629301964919633541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36411688689610479571378885 6827191629301964919633541)
          ·
            refine ⟨1280098430494118422431289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6827191629301964919633541 1280098430494118422431289)
            ·
              refine ⟨960073822870588816823467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280098430494118422431289 960073822870588816823467)
              ·
                refine ⟨1440110734305883225235201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960073822870588816823467 1440110734305883225235201)
                ·
                  refine ⟨1080083050729412418926401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440110734305883225235201 1080083050729412418926401)
                  ·
                    refine ⟨810062288047059314194801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080083050729412418926401 810062288047059314194801)
                    ·
                      refine ⟨607546716035294485646101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810062288047059314194801 607546716035294485646101)
                      ·
                        rfl

theorem cell23_1183193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_1183193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183193 prefixEnd_1183193 := by exact prefixLift 1183193
  have htrace : WordTrace (prefixWord ++ tailWord_1183193) baseStart_1183193 baseEnd_1183193 := by
    simpa [prefixWord, tailWord_1183193, baseEnd_1183193] using wordTrace_append hprefix tailTrace_1183193
  have hstable : (prefixWord ++ tailWord_1183193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183193).length < 2 ^ (prefixWord ++ tailWord_1183193).sum := by decide
  have hdescent : baseEnd_1183193 < baseStart_1183193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183215 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_1183215 : Nat := 118140960795 + 1183215 * 2 ^ 59
def prefixEnd_1183215 : Nat := 4983230072969 + 3 ^ 40 * 1183215 * 2
def baseEnd_1183215 : Nat := 607558012609693399570999

theorem tailTrace_1183215 : CollatzResearch.WordTrace tailWord_1183215 prefixEnd_1183215 607558012609693399570999 := by
  unfold tailWord_1183215
  simp only [CollatzResearch.WordTrace]
  refine ⟨43155396408421606878935099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28770264272281071252623399 43155396408421606878935099)
  ·
    refine ⟨64733094612632410318402649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43155396408421606878935099 64733094612632410318402649)
    ·
      refine ⟨48549820959474307738801987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64733094612632410318402649 48549820959474307738801987)
      ·
        refine ⟨72824731439211461608202981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48549820959474307738801987 72824731439211461608202981)
        ·
          refine ⟨13654637144852149051538059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72824731439211461608202981 13654637144852149051538059)
          ·
            refine ⟨20481955717278223577307089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13654637144852149051538059 20481955717278223577307089)
            ·
              refine ⟨15361466787958667682980317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20481955717278223577307089 15361466787958667682980317)
              ·
                refine ⟨5760550045484500381117619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15361466787958667682980317 5760550045484500381117619)
                ·
                  refine ⟨8640825068226750571676429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760550045484500381117619 8640825068226750571676429)
                  ·
                    refine ⟨3240309400585031464378661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8640825068226750571676429 3240309400585031464378661)
                    ·
                      refine ⟨607558012609693399570999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3240309400585031464378661 607558012609693399570999)
                      ·
                        rfl

theorem cell23_1183215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_1183215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183215 prefixEnd_1183215 := by exact prefixLift 1183215
  have htrace : WordTrace (prefixWord ++ tailWord_1183215) baseStart_1183215 baseEnd_1183215 := by
    simpa [prefixWord, tailWord_1183215, baseEnd_1183215] using wordTrace_append hprefix tailTrace_1183215
  have hstable : (prefixWord ++ tailWord_1183215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183215).length < 2 ^ (prefixWord ++ tailWord_1183215).sum := by decide
  have hdescent : baseEnd_1183215 < baseStart_1183215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183222 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1183222 : Nat := 118140960795 + 1183222 * 2 ^ 59
def prefixEnd_1183222 : Nat := 4983230072969 + 3 ^ 40 * 1183222 * 2
def baseEnd_1183222 : Nat := 607561606974274872183467

theorem tailTrace_1183222 : CollatzResearch.WordTrace tailWord_1183222 prefixEnd_1183222 607561606974274872183467 := by
  unfold tailWord_1183222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697228232462265442152495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28770434479597498049626613 2697228232462265442152495)
  ·
    refine ⟨4045842348693398163228743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697228232462265442152495 4045842348693398163228743)
    ·
      refine ⟨6068763523040097244843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045842348693398163228743 6068763523040097244843115)
      ·
        refine ⟨9103145284560145867264673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068763523040097244843115 9103145284560145867264673)
        ·
          refine ⟨6827358963420109400448505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9103145284560145867264673 6827358963420109400448505)
          ·
            refine ⟨5120519222565082050336379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827358963420109400448505 5120519222565082050336379)
            ·
              refine ⟨7680778833847623075504569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120519222565082050336379 7680778833847623075504569)
              ·
                refine ⟨5760584125385717306628427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7680778833847623075504569 5760584125385717306628427)
                ·
                  refine ⟨8640876188078575959942641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760584125385717306628427 8640876188078575959942641)
                  ·
                    refine ⟨6480657141058931969956981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8640876188078575959942641 6480657141058931969956981)
                    ·
                      refine ⟨607561606974274872183467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6480657141058931969956981 607561606974274872183467)
                      ·
                        rfl

theorem cell23_1183222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1183222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183222 prefixEnd_1183222 := by exact prefixLift 1183222
  have htrace : WordTrace (prefixWord ++ tailWord_1183222) baseStart_1183222 baseEnd_1183222 := by
    simpa [prefixWord, tailWord_1183222, baseEnd_1183222] using wordTrace_append hprefix tailTrace_1183222
  have hstable : (prefixWord ++ tailWord_1183222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183222).length < 2 ^ (prefixWord ++ tailWord_1183222).sum := by decide
  have hdescent : baseEnd_1183222 < baseStart_1183222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183233 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 5]
def baseStart_1183233 : Nat := 118140960795 + 1183233 * 2 ^ 59
def prefixEnd_1183233 : Nat := 4983230072969 + 3 ^ 40 * 1183233 * 2
def baseEnd_1183233 : Nat := 67507472806830481016213

theorem tailTrace_1183233 : CollatzResearch.WordTrace tailWord_1183233 prefixEnd_1183233 67507472806830481016213 := by
  unfold tailWord_1183233
  simp only [CollatzResearch.WordTrace]
  refine ⟨43156052922356395953090353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28770701948237597302060235 43156052922356395953090353)
  ·
    refine ⟨32367039691767296964817765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43156052922356395953090353 32367039691767296964817765)
    ·
      refine ⟨6068819942206368180903331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32367039691767296964817765 6068819942206368180903331)
      ·
        refine ⟨9103229913309552271354997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068819942206368180903331 9103229913309552271354997)
        ·
          refine ⟨853427804372770525439531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9103229913309552271354997 853427804372770525439531)
          ·
            refine ⟨1280141706559155788159297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853427804372770525439531 1280141706559155788159297)
            ·
              refine ⟨960106279919366841119473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280141706559155788159297 960106279919366841119473)
              ·
                refine ⟨720079709939525130839605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960106279919366841119473 720079709939525130839605)
                ·
                  refine ⟨67507472806830481016213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720079709939525130839605 67507472806830481016213)
                  ·
                    rfl

theorem cell23_1183233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 5].length) (baseStart_1183233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183233 prefixEnd_1183233 := by exact prefixLift 1183233
  have htrace : WordTrace (prefixWord ++ tailWord_1183233) baseStart_1183233 baseEnd_1183233 := by
    simpa [prefixWord, tailWord_1183233, baseEnd_1183233] using wordTrace_append hprefix tailTrace_1183233
  have hstable : (prefixWord ++ tailWord_1183233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183233).length < 2 ^ (prefixWord ++ tailWord_1183233).sum := by decide
  have hdescent : baseEnd_1183233 < baseStart_1183233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183289 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 6]
def baseStart_1183289 : Nat := 118140960795 + 1183289 * 2 ^ 59
def prefixEnd_1183289 : Nat := 4983230072969 + 3 ^ 40 * 1183289 * 2
def baseEnd_1183289 : Nat := 67510667797569567782851

theorem tailTrace_1183289 : CollatzResearch.WordTrace tailWord_1183289 prefixEnd_1183289 67510667797569567782851 := by
  unfold tailWord_1183289
  simp only [CollatzResearch.WordTrace]
  refine ⟨43158095410153517517128921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28772063606769011678085947 43158095410153517517128921)
  ·
    refine ⟨32368571557615138137846691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43158095410153517517128921 32368571557615138137846691)
    ·
      refine ⟨48552857336422707206770037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32368571557615138137846691 48552857336422707206770037)
      ·
        refine ⟨4551830375289628800634691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48552857336422707206770037 4551830375289628800634691)
        ·
          refine ⟨6827745562934443200952037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551830375289628800634691 6827745562934443200952037)
          ·
            refine ⟨1280202293050208100178507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6827745562934443200952037 1280202293050208100178507)
            ·
              refine ⟨1920303439575312150267761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280202293050208100178507 1920303439575312150267761)
              ·
                refine ⟨1440227579681484112700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920303439575312150267761 1440227579681484112700821)
                ·
                  refine ⟨67510667797569567782851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1440227579681484112700821 67510667797569567782851)
                  ·
                    rfl

theorem cell23_1183289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_1183289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183289 prefixEnd_1183289 := by exact prefixLift 1183289
  have htrace : WordTrace (prefixWord ++ tailWord_1183289) baseStart_1183289 baseEnd_1183289 := by
    simpa [prefixWord, tailWord_1183289, baseEnd_1183289] using wordTrace_append hprefix tailTrace_1183289
  have hstable : (prefixWord ++ tailWord_1183289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183289).length < 2 ^ (prefixWord ++ tailWord_1183289).sum := by decide
  have hdescent : baseEnd_1183289 < baseStart_1183289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183315 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 7, 6]
def baseStart_1183315 : Nat := 118140960795 + 1183315 * 2 ^ 59
def prefixEnd_1183315 : Nat := 4983230072969 + 3 ^ 40 * 1183315 * 2
def baseEnd_1183315 : Nat := 202536453558381002773513

theorem tailTrace_1183315 : CollatzResearch.WordTrace tailWord_1183315 prefixEnd_1183315 202536453558381002773513 := by
  unfold tailWord_1183315
  simp only [CollatzResearch.WordTrace]
  refine ⟨43159043708059323957575399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28772695805372882638383599 43159043708059323957575399)
  ·
    refine ⟨64738565562088985936363099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43159043708059323957575399 64738565562088985936363099)
    ·
      refine ⟨97107848343133478904544649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64738565562088985936363099 97107848343133478904544649)
      ·
        refine ⟨72830886257350109178408487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97107848343133478904544649 72830886257350109178408487)
        ·
          refine ⟨109246329386025163767612731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72830886257350109178408487 109246329386025163767612731)
          ·
            refine ⟨163869494079037745651419097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109246329386025163767612731 163869494079037745651419097)
            ·
              refine ⟨122902120559278309238564323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163869494079037745651419097 122902120559278309238564323)
              ·
                refine ⟨184353180838917463857846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122902120559278309238564323 184353180838917463857846485)
                ·
                  refine ⟨4320777675912128059168277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184353180838917463857846485 4320777675912128059168277)
                  ·
                    refine ⟨202536453558381002773513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4320777675912128059168277 202536453558381002773513)
                    ·
                      rfl

theorem cell23_1183315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_1183315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183315 prefixEnd_1183315 := by exact prefixLift 1183315
  have htrace : WordTrace (prefixWord ++ tailWord_1183315) baseStart_1183315 baseEnd_1183315 := by
    simpa [prefixWord, tailWord_1183315, baseEnd_1183315] using wordTrace_append hprefix tailTrace_1183315
  have hstable : (prefixWord ++ tailWord_1183315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183315).length < 2 ^ (prefixWord ++ tailWord_1183315).sum := by decide
  have hdescent : baseEnd_1183315 < baseStart_1183315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183319 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 1, 5]
def baseStart_1183319 : Nat := 118140960795 + 1183319 * 2 ^ 59
def prefixEnd_1183319 : Nat := 4983230072969 + 3 ^ 40 * 1183319 * 2
def baseEnd_1183319 : Nat := 202537138199253664223507

theorem tailTrace_1183319 : CollatzResearch.WordTrace tailWord_1183319 prefixEnd_1183319 202537138199253664223507 := by
  unfold tailWord_1183319
  simp only [CollatzResearch.WordTrace]
  refine ⟨43159189600044832640721011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28772793066696555093814007 43159189600044832640721011)
  ·
    refine ⟨64738784400067248961081517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43159189600044832640721011 64738784400067248961081517)
    ·
      refine ⟨24277044150025218360405569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64738784400067248961081517 24277044150025218360405569)
      ·
        refine ⟨18207783112518913770304177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24277044150025218360405569 18207783112518913770304177)
        ·
          refine ⟨13655837334389185327728133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18207783112518913770304177 13655837334389185327728133)
          ·
            refine ⟨2560469500197972248949025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13655837334389185327728133 2560469500197972248949025)
            ·
              refine ⟨1920352125148479186711769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560469500197972248949025 1920352125148479186711769)
              ·
                refine ⟨1440264093861359390033827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920352125148479186711769 1440264093861359390033827)
                ·
                  refine ⟨2160396140792039085050741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440264093861359390033827 2160396140792039085050741)
                  ·
                    refine ⟨202537138199253664223507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2160396140792039085050741 202537138199253664223507)
                    ·
                      rfl

theorem cell23_1183319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_1183319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183319 prefixEnd_1183319 := by exact prefixLift 1183319
  have htrace : WordTrace (prefixWord ++ tailWord_1183319) baseStart_1183319 baseEnd_1183319 := by
    simpa [prefixWord, tailWord_1183319, baseEnd_1183319] using wordTrace_append hprefix tailTrace_1183319
  have hstable : (prefixWord ++ tailWord_1183319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183319).length < 2 ^ (prefixWord ++ tailWord_1183319).sum := by decide
  have hdescent : baseEnd_1183319 < baseStart_1183319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183322 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1183322 : Nat := 118140960795 + 1183322 * 2 ^ 59
def prefixEnd_1183322 : Nat := 4983230072969 + 3 ^ 40 * 1183322 * 2
def baseEnd_1183322 : Nat := 607612955039724480933007

theorem tailTrace_1183322 : CollatzResearch.WordTrace tailWord_1183322 prefixEnd_1183322 607612955039724480933007 := by
  unfold tailWord_1183322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789824754758491038270055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28772866012689309435386813 10789824754758491038270055)
  ·
    refine ⟨16184737132137736557405083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10789824754758491038270055 16184737132137736557405083)
    ·
      refine ⟨24277105698206604836107625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16184737132137736557405083 24277105698206604836107625)
      ·
        refine ⟨18207829273654953627080719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24277105698206604836107625 18207829273654953627080719)
        ·
          refine ⟨27311743910482430440621079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18207829273654953627080719 27311743910482430440621079)
          ·
            refine ⟨40967615865723645660931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27311743910482430440621079 40967615865723645660931619)
            ·
              refine ⟨61451423798585468491397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40967615865723645660931619 61451423798585468491397429)
              ·
                refine ⟨5761070981117387671068509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61451423798585468491397429 5761070981117387671068509)
                ·
                  refine ⟨2160401617919020376650691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5761070981117387671068509 2160401617919020376650691)
                  ·
                    refine ⟨3240602426878530564976037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160401617919020376650691 3240602426878530564976037)
                    ·
                      refine ⟨607612955039724480933007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3240602426878530564976037 607612955039724480933007)
                      ·
                        rfl

theorem cell23_1183322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1183322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183322 prefixEnd_1183322 := by exact prefixLift 1183322
  have htrace : WordTrace (prefixWord ++ tailWord_1183322) baseStart_1183322 baseEnd_1183322 := by
    simpa [prefixWord, tailWord_1183322, baseEnd_1183322] using wordTrace_append hprefix tailTrace_1183322
  have hstable : (prefixWord ++ tailWord_1183322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183322).length < 2 ^ (prefixWord ++ tailWord_1183322).sum := by decide
  have hdescent : baseEnd_1183322 < baseStart_1183322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183333 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_1183333 : Nat := 118140960795 + 1183333 * 2 ^ 59
def prefixEnd_1183333 : Nat := 4983230072969 + 3 ^ 40 * 1183333 * 2
def baseEnd_1183333 : Nat := 607618603326923937895457

theorem tailTrace_1183333 : CollatzResearch.WordTrace tailWord_1183333 prefixEnd_1183333 607618603326923937895457 := by
  unfold tailWord_1183333
  simp only [CollatzResearch.WordTrace]
  refine ⟨43159700221994113031730653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28773133481329408687820435 43159700221994113031730653)
  ·
    refine ⟨16184887583247792386898995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43159700221994113031730653 16184887583247792386898995)
    ·
      refine ⟨24277331374871688580348493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16184887583247792386898995 24277331374871688580348493)
      ·
        refine ⟨9103999265576883217630685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24277331374871688580348493 9103999265576883217630685)
        ·
          refine ⟨3413999724591331206611507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9103999265576883217630685 3413999724591331206611507)
          ·
            refine ⟨5120999586886996809917261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413999724591331206611507 5120999586886996809917261)
            ·
              refine ⟨1920374845082623803718973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5120999586886996809917261 1920374845082623803718973)
              ·
                refine ⟨720140566905983926394615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1920374845082623803718973 720140566905983926394615)
                ·
                  refine ⟨1080210850358975889591923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720140566905983926394615 1080210850358975889591923)
                  ·
                    refine ⟨1620316275538463834387885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1080210850358975889591923 1620316275538463834387885)
                    ·
                      refine ⟨607618603326923937895457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620316275538463834387885 607618603326923937895457)
                      ·
                        rfl

theorem cell23_1183333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_1183333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183333 prefixEnd_1183333 := by exact prefixLift 1183333
  have htrace : WordTrace (prefixWord ++ tailWord_1183333) baseStart_1183333 baseEnd_1183333 := by
    simpa [prefixWord, tailWord_1183333, baseEnd_1183333] using wordTrace_append hprefix tailTrace_1183333
  have hstable : (prefixWord ++ tailWord_1183333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183333).length < 2 ^ (prefixWord ++ tailWord_1183333).sum := by decide
  have hdescent : baseEnd_1183333 < baseStart_1183333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183393 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1183393 : Nat := 118140960795 + 1183393 * 2 ^ 59
def prefixEnd_1183393 : Nat := 4983230072969 + 3 ^ 40 * 1183393 * 2
def baseEnd_1183393 : Nat := 607649412166193703145181

theorem tailTrace_1183393 : CollatzResearch.WordTrace tailWord_1183393 prefixEnd_1183393 607649412166193703145181 := by
  unfold tailWord_1183393
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161888601776743278914833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28774592401184495519276555 43161888601776743278914833)
  ·
    refine ⟨32371416451332557459186125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43161888601776743278914833 32371416451332557459186125)
    ·
      refine ⟨12139281169249709047194797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32371416451332557459186125 12139281169249709047194797)
      ·
        refine ⟨4552230438468640892698049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12139281169249709047194797 4552230438468640892698049)
        ·
          refine ⟨3414172828851480669523537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4552230438468640892698049 3414172828851480669523537)
          ·
            refine ⟨2560629621638610502142653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414172828851480669523537 2560629621638610502142653)
            ·
              refine ⟨960236108114478938303495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560629621638610502142653 960236108114478938303495)
              ·
                refine ⟨1440354162171718407455243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960236108114478938303495 1440354162171718407455243)
                ·
                  refine ⟨2160531243257577611182865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440354162171718407455243 2160531243257577611182865)
                  ·
                    refine ⟨1620398432443183208387149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160531243257577611182865 1620398432443183208387149)
                    ·
                      refine ⟨607649412166193703145181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620398432443183208387149 607649412166193703145181)
                      ·
                        rfl

theorem cell23_1183393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1183393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183393 prefixEnd_1183393 := by exact prefixLift 1183393
  have htrace : WordTrace (prefixWord ++ tailWord_1183393) baseStart_1183393 baseEnd_1183393 := by
    simpa [prefixWord, tailWord_1183393, baseEnd_1183393] using wordTrace_append hprefix tailTrace_1183393
  have hstable : (prefixWord ++ tailWord_1183393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183393).length < 2 ^ (prefixWord ++ tailWord_1183393).sum := by decide
  have hdescent : baseEnd_1183393 < baseStart_1183393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183429 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_1183429 : Nat := 118140960795 + 1183429 * 2 ^ 59
def prefixEnd_1183429 : Nat := 4983230072969 + 3 ^ 40 * 1183429 * 2
def baseEnd_1183429 : Nat := 607667897469755562295015

theorem tailTrace_1183429 : CollatzResearch.WordTrace tailWord_1183429 prefixEnd_1183429 607667897469755562295015 := by
  unfold tailWord_1183429
  simp only [CollatzResearch.WordTrace]
  refine ⟨43163201629646321427225341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28775467753097547618150227 43163201629646321427225341)
  ·
    refine ⟨16186200611117370535209503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43163201629646321427225341 16186200611117370535209503)
    ·
      refine ⟨24279300916676055802814255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186200611117370535209503 24279300916676055802814255)
      ·
        refine ⟨36418951375014083704221383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24279300916676055802814255 36418951375014083704221383)
        ·
          refine ⟨54628427062521125556332075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36418951375014083704221383 54628427062521125556332075)
          ·
            refine ⟨81942640593781688334498113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54628427062521125556332075 81942640593781688334498113)
            ·
              refine ⟨61456980445336266250873585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81942640593781688334498113 61456980445336266250873585)
              ·
                refine ⟨46092735334002199688155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61456980445336266250873585 46092735334002199688155189)
                ·
                  refine ⟨4321193937562706220764549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46092735334002199688155189 4321193937562706220764549)
                  ·
                    refine ⟨810223863293007416393353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4321193937562706220764549 810223863293007416393353)
                    ·
                      refine ⟨607667897469755562295015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810223863293007416393353 607667897469755562295015)
                      ·
                        rfl

theorem cell23_1183429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_1183429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183429 prefixEnd_1183429 := by exact prefixLift 1183429
  have htrace : WordTrace (prefixWord ++ tailWord_1183429) baseStart_1183429 baseEnd_1183429 := by
    simpa [prefixWord, tailWord_1183429, baseEnd_1183429] using wordTrace_append hprefix tailTrace_1183429
  have hstable : (prefixWord ++ tailWord_1183429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183429).length < 2 ^ (prefixWord ++ tailWord_1183429).sum := by decide
  have hdescent : baseEnd_1183429 < baseStart_1183429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183450 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_1183450 : Nat := 118140960795 + 1183450 * 2 ^ 59
def prefixEnd_1183450 : Nat := 4983230072969 + 3 ^ 40 * 1183450 * 2
def baseEnd_1183450 : Nat := 607678680563499980132419

theorem tailTrace_1183450 : CollatzResearch.WordTrace tailWord_1183450 prefixEnd_1183450 607678680563499980132419 := by
  unfold tailWord_1183450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10790991890642560503434951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28775978375046828009159869 10790991890642560503434951)
  ·
    refine ⟨16186487835963840755152427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10790991890642560503434951 16186487835963840755152427)
    ·
      refine ⟨24279731753945761132728641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16186487835963840755152427 24279731753945761132728641)
      ·
        refine ⟨18209798815459320849546481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24279731753945761132728641 18209798815459320849546481)
        ·
          refine ⟨13657349111594490637159861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18209798815459320849546481 13657349111594490637159861)
          ·
            refine ⟨1280376479211983497233737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13657349111594490637159861 1280376479211983497233737)
            ·
              refine ⟨960282359408987622925303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280376479211983497233737 960282359408987622925303)
              ·
                refine ⟨1440423539113481434387955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960282359408987622925303 1440423539113481434387955)
                ·
                  refine ⟨2160635308670222151581933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440423539113481434387955 2160635308670222151581933)
                  ·
                    refine ⟨810238240751333306843225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2160635308670222151581933 810238240751333306843225)
                    ·
                      refine ⟨607678680563499980132419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810238240751333306843225 607678680563499980132419)
                      ·
                        rfl

theorem cell23_1183450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_1183450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183450 prefixEnd_1183450 := by exact prefixLift 1183450
  have htrace : WordTrace (prefixWord ++ tailWord_1183450) baseStart_1183450 baseEnd_1183450 := by
    simpa [prefixWord, tailWord_1183450, baseEnd_1183450] using wordTrace_append hprefix tailTrace_1183450
  have hstable : (prefixWord ++ tailWord_1183450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183450).length < 2 ^ (prefixWord ++ tailWord_1183450).sum := by decide
  have hdescent : baseEnd_1183450 < baseStart_1183450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183469 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1183469 : Nat := 118140960795 + 1183469 * 2 ^ 59
def prefixEnd_1183469 : Nat := 4983230072969 + 3 ^ 40 * 1183469 * 2
def baseEnd_1183469 : Nat := 67520937410659489532759

theorem tailTrace_1183469 : CollatzResearch.WordTrace tailWord_1183469 prefixEnd_1183469 67520937410659489532759 := by
  unfold tailWord_1183469
  simp only [CollatzResearch.WordTrace]
  refine ⟨43164660549501408258681461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28776440366334272172454307 43164660549501408258681461)
  ·
    refine ⟨4046686926515757024251387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43164660549501408258681461 4046686926515757024251387)
    ·
      refine ⟨6070030389773635536377081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046686926515757024251387 6070030389773635536377081)
      ·
        refine ⟨4552522792330226652282811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6070030389773635536377081 4552522792330226652282811)
        ·
          refine ⟨6828784188495339978424217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4552522792330226652282811 6828784188495339978424217)
          ·
            refine ⟨5121588141371504983818163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6828784188495339978424217 5121588141371504983818163)
            ·
              refine ⟨7682382212057257475727245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121588141371504983818163 7682382212057257475727245)
              ·
                refine ⟨2880893329521471553397717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7682382212057257475727245 2880893329521471553397717)
                ·
                  refine ⟨67520937410659489532759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2880893329521471553397717 67520937410659489532759)
                  ·
                    rfl

theorem cell23_1183469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1183469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183469 prefixEnd_1183469 := by exact prefixLift 1183469
  have htrace : WordTrace (prefixWord ++ tailWord_1183469) baseStart_1183469 baseEnd_1183469 := by
    simpa [prefixWord, tailWord_1183469, baseEnd_1183469] using wordTrace_append hprefix tailTrace_1183469
  have hstable : (prefixWord ++ tailWord_1183469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183469).length < 2 ^ (prefixWord ++ tailWord_1183469).sum := by decide
  have hdescent : baseEnd_1183469 < baseStart_1183469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183479 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_1183479 : Nat := 118140960795 + 1183479 * 2 ^ 59
def prefixEnd_1183479 : Nat := 4983230072969 + 3 ^ 40 * 1183479 * 2
def baseEnd_1183479 : Nat := 607693571502480366669785

theorem tailTrace_1183479 : CollatzResearch.WordTrace tailWord_1183479 prefixEnd_1183479 607693571502480366669785 := by
  unfold tailWord_1183479
  simp only [CollatzResearch.WordTrace]
  refine ⟨43165025279465179966545491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28776683519643453311030327 43165025279465179966545491)
  ·
    refine ⟨64747537919197769949818237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43165025279465179966545491 64747537919197769949818237)
    ·
      refine ⟨24280326719699163731181839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64747537919197769949818237 24280326719699163731181839)
      ·
        refine ⟨36420490079548745596772759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24280326719699163731181839 36420490079548745596772759)
        ·
          refine ⟨54630735119323118395159139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36420490079548745596772759 54630735119323118395159139)
          ·
            refine ⟨81946102678984677592738709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54630735119323118395159139 81946102678984677592738709)
            ·
              refine ⟨3841223563077406762159627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81946102678984677592738709 3841223563077406762159627)
              ·
                refine ⟨5761835344616110143239441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841223563077406762159627 5761835344616110143239441)
                ·
                  refine ⟨4321376508462082607429581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5761835344616110143239441 4321376508462082607429581)
                  ·
                    refine ⟨1620516190673280977786093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4321376508462082607429581 1620516190673280977786093)
                    ·
                      refine ⟨607693571502480366669785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620516190673280977786093 607693571502480366669785)
                      ·
                        rfl

theorem cell23_1183479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_1183479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183479 prefixEnd_1183479 := by exact prefixLift 1183479
  have htrace : WordTrace (prefixWord ++ tailWord_1183479) baseStart_1183479 baseEnd_1183479 := by
    simpa [prefixWord, tailWord_1183479, baseEnd_1183479] using wordTrace_append hprefix tailTrace_1183479
  have hstable : (prefixWord ++ tailWord_1183479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183479).length < 2 ^ (prefixWord ++ tailWord_1183479).sum := by decide
  have hdescent : baseEnd_1183479 < baseStart_1183479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183620 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_1183620 : Nat := 118140960795 + 1183620 * 2 ^ 59
def prefixEnd_1183620 : Nat := 4983230072969 + 3 ^ 40 * 1183620 * 2
def baseEnd_1183620 : Nat := 607765972274764315006637

theorem tailTrace_1183620 : CollatzResearch.WordTrace tailWord_1183620 prefixEnd_1183620 607765972274764315006637 := by
  unfold tailWord_1183620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585083985977180523714157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28780111981302907364952209 21585083985977180523714157)
  ·
    refine ⟨8094406494741442696392809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21585083985977180523714157 8094406494741442696392809)
    ·
      refine ⟨6070804871056082022294607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8094406494741442696392809 6070804871056082022294607)
      ·
        refine ⟨9106207306584123033441911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070804871056082022294607 9106207306584123033441911)
        ·
          refine ⟨13659310959876184550162867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9106207306584123033441911 13659310959876184550162867)
          ·
            refine ⟨20488966439814276825244301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13659310959876184550162867 20488966439814276825244301)
            ·
              refine ⟨7683362414930353809466613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20488966439814276825244301 7683362414930353809466613)
              ·
                refine ⟨720315226399720669637495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7683362414930353809466613 720315226399720669637495)
                ·
                  refine ⟨1080472839599581004456243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720315226399720669637495 1080472839599581004456243)
                  ·
                    refine ⟨1620709259399371506684365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1080472839599581004456243 1620709259399371506684365)
                    ·
                      refine ⟨607765972274764315006637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620709259399371506684365 607765972274764315006637)
                      ·
                        rfl

theorem cell23_1183620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_1183620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183620 prefixEnd_1183620 := by exact prefixLift 1183620
  have htrace : WordTrace (prefixWord ++ tailWord_1183620) baseStart_1183620 baseEnd_1183620 := by
    simpa [prefixWord, tailWord_1183620, baseEnd_1183620] using wordTrace_append hprefix tailTrace_1183620
  have hstable : (prefixWord ++ tailWord_1183620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183620).length < 2 ^ (prefixWord ++ tailWord_1183620).sum := by decide
  have hdescent : baseEnd_1183620 < baseStart_1183620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183623 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 1, 5]
def baseStart_1183623 : Nat := 118140960795 + 1183623 * 2 ^ 59
def prefixEnd_1183623 : Nat := 4983230072969 + 3 ^ 40 * 1183623 * 2
def baseEnd_1183623 : Nat := 202589170905575934423041

theorem tailTrace_1183623 : CollatzResearch.WordTrace tailWord_1183623 prefixEnd_1183623 202589170905575934423041 := by
  unfold tailWord_1183623
  simp only [CollatzResearch.WordTrace]
  refine ⟨43170277390943492559787523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28780184927295661706525015 43170277390943492559787523)
  ·
    refine ⟨64755416086415238839681285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43170277390943492559787523 64755416086415238839681285)
    ·
      refine ⟨12141640516202857282440241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64755416086415238839681285 12141640516202857282440241)
      ·
        refine ⟨9106230387152142961830181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12141640516202857282440241 9106230387152142961830181)
        ·
          refine ⟨1707418197591026805343159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9106230387152142961830181 1707418197591026805343159)
          ·
            refine ⟨2561127296386540208014739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707418197591026805343159 2561127296386540208014739)
            ·
              refine ⟨3841690944579810312022109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561127296386540208014739 3841690944579810312022109)
              ·
                refine ⟨1440634104217428867008291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3841690944579810312022109 1440634104217428867008291)
                ·
                  refine ⟨2160951156326143300512437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440634104217428867008291 2160951156326143300512437)
                  ·
                    refine ⟨202589170905575934423041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2160951156326143300512437 202589170905575934423041)
                    ·
                      rfl

theorem cell23_1183623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_1183623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183623 prefixEnd_1183623 := by exact prefixLift 1183623
  have htrace : WordTrace (prefixWord ++ tailWord_1183623) baseStart_1183623 baseEnd_1183623 := by
    simpa [prefixWord, tailWord_1183623, baseEnd_1183623] using wordTrace_append hprefix tailTrace_1183623
  have hstable : (prefixWord ++ tailWord_1183623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183623).length < 2 ^ (prefixWord ++ tailWord_1183623).sum := by decide
  have hdescent : baseEnd_1183623 < baseStart_1183623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183663 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_1183663 : Nat := 118140960795 + 1183663 * 2 ^ 59
def prefixEnd_1183663 : Nat := 4983230072969 + 3 ^ 40 * 1183663 * 2
def baseEnd_1183663 : Nat := 607788051942907646768939

theorem tailTrace_1183663 : CollatzResearch.WordTrace tailWord_1183663 prefixEnd_1183663 607788051942907646768939 := by
  unfold tailWord_1183663
  simp only [CollatzResearch.WordTrace]
  refine ⟨43171736310798579391243643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28781157540532386260829095 43171736310798579391243643)
  ·
    refine ⟨64757604466197869086865465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43171736310798579391243643 64757604466197869086865465)
    ·
      refine ⟨48568203349648401815149099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64757604466197869086865465 48568203349648401815149099)
      ·
        refine ⟨72852305024472602722723649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48568203349648401815149099 72852305024472602722723649)
        ·
          refine ⟨54639228768354452042042737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72852305024472602722723649 54639228768354452042042737)
          ·
            refine ⟨40979421576265839031532053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54639228768354452042042737 40979421576265839031532053)
            ·
              refine ⟨1920910386387461204603065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40979421576265839031532053 1920910386387461204603065)
              ·
                refine ⟨1440682789790595903452299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920910386387461204603065 1440682789790595903452299)
                ·
                  refine ⟨2161024184685893855178449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440682789790595903452299 2161024184685893855178449)
                  ·
                    refine ⟨1620768138514420391383837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2161024184685893855178449 1620768138514420391383837)
                    ·
                      refine ⟨607788051942907646768939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620768138514420391383837 607788051942907646768939)
                      ·
                        rfl

theorem cell23_1183663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_1183663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183663 prefixEnd_1183663 := by exact prefixLift 1183663
  have htrace : WordTrace (prefixWord ++ tailWord_1183663) baseStart_1183663 baseEnd_1183663 := by
    simpa [prefixWord, tailWord_1183663, baseEnd_1183663] using wordTrace_append hprefix tailTrace_1183663
  have hstable : (prefixWord ++ tailWord_1183663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183663).length < 2 ^ (prefixWord ++ tailWord_1183663).sum := by decide
  have hdescent : baseEnd_1183663 < baseStart_1183663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183694 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_1183694 : Nat := 118140960795 + 1183694 * 2 ^ 59
def prefixEnd_1183694 : Nat := 4983230072969 + 3 ^ 40 * 1183694 * 2
def baseEnd_1183694 : Nat := 607803969843197025481297

theorem tailTrace_1183694 : CollatzResearch.WordTrace tailWord_1183694 prefixEnd_1183694 607803969843197025481297 := by
  unfold tailWord_1183694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396608371710783960702767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28781911315790847790414757 5396608371710783960702767)
  ·
    refine ⟨8094912557566175941054151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5396608371710783960702767 8094912557566175941054151)
    ·
      refine ⟨12142368836349263911581227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8094912557566175941054151 12142368836349263911581227)
      ·
        refine ⟨18213553254523895867371841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12142368836349263911581227 18213553254523895867371841)
        ·
          refine ⟨13660164940892921900528881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18213553254523895867371841 13660164940892921900528881)
          ·
            refine ⟨10245123705669691425396661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13660164940892921900528881 10245123705669691425396661)
            ·
              refine ⟨960480347406533571130937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10245123705669691425396661 960480347406533571130937)
              ·
                refine ⟨720360260554900178348203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960480347406533571130937 720360260554900178348203)
                ·
                  refine ⟨1080540390832350267522305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720360260554900178348203 1080540390832350267522305)
                  ·
                    refine ⟨810405293124262700641729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080540390832350267522305 810405293124262700641729)
                    ·
                      refine ⟨607803969843197025481297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810405293124262700641729 607803969843197025481297)
                      ·
                        rfl

theorem cell23_1183694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_1183694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183694 prefixEnd_1183694 := by exact prefixLift 1183694
  have htrace : WordTrace (prefixWord ++ tailWord_1183694) baseStart_1183694 baseEnd_1183694 := by
    simpa [prefixWord, tailWord_1183694, baseEnd_1183694] using wordTrace_append hprefix tailTrace_1183694
  have hstable : (prefixWord ++ tailWord_1183694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183694).length < 2 ^ (prefixWord ++ tailWord_1183694).sum := by decide
  have hdescent : baseEnd_1183694 < baseStart_1183694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183703 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_1183703 : Nat := 118140960795 + 1183703 * 2 ^ 59
def prefixEnd_1183703 : Nat := 4983230072969 + 3 ^ 40 * 1183703 * 2
def baseEnd_1183703 : Nat := 607808591169087490268755

theorem tailTrace_1183703 : CollatzResearch.WordTrace tailWord_1183703 prefixEnd_1183703 607808591169087490268755 := by
  unfold tailWord_1183703
  simp only [CollatzResearch.WordTrace]
  refine ⟨43173195230653666222699763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28782130153769110815133175 43173195230653666222699763)
  ·
    refine ⟨64759792845980499334049645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43173195230653666222699763 64759792845980499334049645)
    ·
      refine ⟨24284922317242687250268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64759792845980499334049645 24284922317242687250268617)
      ·
        refine ⟨18213691737932015437701463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24284922317242687250268617 18213691737932015437701463)
        ·
          refine ⟨27320537606898023156552195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18213691737932015437701463 27320537606898023156552195)
          ·
            refine ⟨40980806410347034734828293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27320537606898023156552195 40980806410347034734828293)
            ·
              refine ⟨7683901201940069012780305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40980806410347034734828293 7683901201940069012780305)
              ·
                refine ⟨5762925901455051759585229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7683901201940069012780305 5762925901455051759585229)
                ·
                  refine ⟨2161097213045644409844461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5762925901455051759585229 2161097213045644409844461)
                  ·
                    refine ⟨810411454892116653691673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161097213045644409844461 810411454892116653691673)
                    ·
                      refine ⟨607808591169087490268755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810411454892116653691673 607808591169087490268755)
                      ·
                        rfl

theorem cell23_1183703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_1183703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183703 prefixEnd_1183703 := by exact prefixLift 1183703
  have htrace : WordTrace (prefixWord ++ tailWord_1183703) baseStart_1183703 baseEnd_1183703 := by
    simpa [prefixWord, tailWord_1183703, baseEnd_1183703] using wordTrace_append hprefix tailTrace_1183703
  have hstable : (prefixWord ++ tailWord_1183703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183703).length < 2 ^ (prefixWord ++ tailWord_1183703).sum := by decide
  have hdescent : baseEnd_1183703 < baseStart_1183703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183714 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1183714 : Nat := 118140960795 + 1183714 * 2 ^ 59
def prefixEnd_1183714 : Nat := 4983230072969 + 3 ^ 40 * 1183714 * 2
def baseEnd_1183714 : Nat := 607814239456286947231205

theorem tailTrace_1183714 : CollatzResearch.WordTrace tailWord_1183714 prefixEnd_1183714 607814239456286947231205 := by
  unfold tailWord_1183714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10793399108403453775337549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28782397622409210067566797 10793399108403453775337549)
  ·
    refine ⟨4047524665651295165751581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10793399108403453775337549 4047524665651295165751581)
    ·
      refine ⟨1517821749619235687156843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4047524665651295165751581 1517821749619235687156843)
      ·
        refine ⟨2276732624428853530735265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517821749619235687156843 2276732624428853530735265)
        ·
          refine ⟨1707549468321640148051449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276732624428853530735265 1707549468321640148051449)
          ·
            refine ⟨1280662101241230111038587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707549468321640148051449 1280662101241230111038587)
            ·
              refine ⟨1920993151861845166557881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280662101241230111038587 1920993151861845166557881)
              ·
                refine ⟨1440744863896383874918411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920993151861845166557881 1440744863896383874918411)
                ·
                  refine ⟨2161117295844575812377617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440744863896383874918411 2161117295844575812377617)
                  ·
                    refine ⟨1620837971883431859283213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2161117295844575812377617 1620837971883431859283213)
                    ·
                      refine ⟨607814239456286947231205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1620837971883431859283213 607814239456286947231205)
                      ·
                        rfl

theorem cell23_1183714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1183714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183714 prefixEnd_1183714 := by exact prefixLift 1183714
  have htrace : WordTrace (prefixWord ++ tailWord_1183714) baseStart_1183714 baseEnd_1183714 := by
    simpa [prefixWord, tailWord_1183714, baseEnd_1183714] using wordTrace_append hprefix tailTrace_1183714
  have hstable : (prefixWord ++ tailWord_1183714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183714).length < 2 ^ (prefixWord ++ tailWord_1183714).sum := by decide
  have hdescent : baseEnd_1183714 < baseStart_1183714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183736 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1183736 : Nat := 118140960795 + 1183736 * 2 ^ 59
def prefixEnd_1183736 : Nat := 4983230072969 + 3 ^ 40 * 1183736 * 2
def baseEnd_1183736 : Nat := 607825536030685861156103

theorem tailTrace_1183736 : CollatzResearch.WordTrace tailWord_1183736 prefixEnd_1183736 607825536030685861156103 := by
  unfold tailWord_1183736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21587199419767056429325531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28782932559689408572434041 21587199419767056429325531)
  ·
    refine ⟨32380799129650584643988297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21587199419767056429325531 32380799129650584643988297)
    ·
      refine ⟨24285599347237938482991223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32380799129650584643988297 24285599347237938482991223)
      ·
        refine ⟨36428399020856907724486835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24285599347237938482991223 36428399020856907724486835)
        ·
          refine ⟨54642598531285361586730253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36428399020856907724486835 54642598531285361586730253)
          ·
            refine ⟨20490974449232010595023845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54642598531285361586730253 20490974449232010595023845)
            ·
              refine ⟨3842057709231001986566971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20490974449232010595023845 3842057709231001986566971)
              ·
                refine ⟨5763086563846502979850457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842057709231001986566971 5763086563846502979850457)
                ·
                  refine ⟨4322314922884877234887843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5763086563846502979850457 4322314922884877234887843)
                  ·
                    refine ⟨6483472384327315852331765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4322314922884877234887843 6483472384327315852331765)
                    ·
                      refine ⟨607825536030685861156103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6483472384327315852331765 607825536030685861156103)
                      ·
                        rfl

theorem cell23_1183736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1183736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183736 prefixEnd_1183736 := by exact prefixLift 1183736
  have htrace : WordTrace (prefixWord ++ tailWord_1183736) baseStart_1183736 baseEnd_1183736 := by
    simpa [prefixWord, tailWord_1183736, baseEnd_1183736] using wordTrace_append hprefix tailTrace_1183736
  have hstable : (prefixWord ++ tailWord_1183736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183736).length < 2 ^ (prefixWord ++ tailWord_1183736).sum := by decide
  have hdescent : baseEnd_1183736 < baseStart_1183736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183737 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 1, 3, 2]
def baseStart_1183737 : Nat := 118140960795 + 1183737 * 2 ^ 59
def prefixEnd_1183737 : Nat := 4983230072969 + 3 ^ 40 * 1183737 * 2
def baseEnd_1183737 : Nat := 607826049511340357243599

theorem tailTrace_1183737 : CollatzResearch.WordTrace tailWord_1183737 prefixEnd_1183737 607826049511340357243599 := by
  unfold tailWord_1183737
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174435312530490029437465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28782956875020326686291643 43174435312530490029437465)
  ·
    refine ⟨32380826484397867522078099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43174435312530490029437465 32380826484397867522078099)
    ·
      refine ⟨48571239726596801283117149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32380826484397867522078099 48571239726596801283117149)
      ·
        refine ⟨18214214897473800481168931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48571239726596801283117149 18214214897473800481168931)
        ·
          refine ⟨27321322346210700721753397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18214214897473800481168931 27321322346210700721753397)
          ·
            refine ⟨2561373969957253192664381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27321322346210700721753397 2561373969957253192664381)
            ·
              refine ⟨960515238733969947249143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2561373969957253192664381 960515238733969947249143)
              ·
                refine ⟨1440772858100954920873715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960515238733969947249143 1440772858100954920873715)
                ·
                  refine ⟨2161159287151432381310573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440772858100954920873715 2161159287151432381310573)
                  ·
                    refine ⟨810434732681787142991465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161159287151432381310573 810434732681787142991465)
                    ·
                      refine ⟨607826049511340357243599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810434732681787142991465 607826049511340357243599)
                      ·
                        rfl

theorem cell23_1183737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_1183737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183737 prefixEnd_1183737 := by exact prefixLift 1183737
  have htrace : WordTrace (prefixWord ++ tailWord_1183737) baseStart_1183737 baseEnd_1183737 := by
    simpa [prefixWord, tailWord_1183737, baseEnd_1183737] using wordTrace_append hprefix tailTrace_1183737
  have hstable : (prefixWord ++ tailWord_1183737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183737).length < 2 ^ (prefixWord ++ tailWord_1183737).sum := by decide
  have hdescent : baseEnd_1183737 < baseStart_1183737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183756 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 7]
def baseStart_1183756 : Nat := 118140960795 + 1183756 * 2 ^ 59
def prefixEnd_1183756 : Nat := 4983230072969 + 3 ^ 40 * 1183756 * 2
def baseEnd_1183756 : Nat := 67537311738197309211779

theorem tailTrace_1183756 : CollatzResearch.WordTrace tailWord_1183756 prefixEnd_1183756 67537311738197309211779 := by
  unfold tailWord_1183756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21587564149730828137189561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28783418866307770849586081 21587564149730828137189561)
  ·
    refine ⟨16190673112298121102892171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21587564149730828137189561 16190673112298121102892171)
    ·
      refine ⟨24286009668447181654338257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16190673112298121102892171 24286009668447181654338257)
      ·
        refine ⟨18214507251335386240753693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24286009668447181654338257 18214507251335386240753693)
        ·
          refine ⟨6830440219250769840282635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18214507251335386240753693 6830440219250769840282635)
          ·
            refine ⟨10245660328876154760423953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6830440219250769840282635 10245660328876154760423953)
            ·
              refine ⟨7684245246657116070317965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10245660328876154760423953 7684245246657116070317965)
              ·
                refine ⟨2881591967496418526369237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7684245246657116070317965 2881591967496418526369237)
                ·
                  refine ⟨67537311738197309211779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2881591967496418526369237 67537311738197309211779)
                  ·
                    rfl

theorem cell23_1183756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_1183756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183756 prefixEnd_1183756 := by exact prefixLift 1183756
  have htrace : WordTrace (prefixWord ++ tailWord_1183756) baseStart_1183756 baseEnd_1183756 := by
    simpa [prefixWord, tailWord_1183756, baseEnd_1183756] using wordTrace_append hprefix tailTrace_1183756
  have hstable : (prefixWord ++ tailWord_1183756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183756).length < 2 ^ (prefixWord ++ tailWord_1183756).sum := by decide
  have hdescent : baseEnd_1183756 < baseStart_1183756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183767 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1183767 : Nat := 118140960795 + 1183767 * 2 ^ 59
def prefixEnd_1183767 : Nat := 4983230072969 + 3 ^ 40 * 1183767 * 2
def baseEnd_1183767 : Nat := 607841453930975239868461

theorem tailTrace_1183767 : CollatzResearch.WordTrace tailWord_1183767 prefixEnd_1183767 607841453930975239868461 := by
  unfold tailWord_1183767
  simp only [CollatzResearch.WordTrace]
  refine ⟨43175529502421805153029555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28783686334947870102019703 43175529502421805153029555)
  ·
    refine ⟨64763294253632707729544333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43175529502421805153029555 64763294253632707729544333)
    ·
      refine ⟨24286235345112265398579125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64763294253632707729544333 24286235345112265398579125)
      ·
        refine ⟨2276834563604274881116793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24286235345112265398579125 2276834563604274881116793)
        ·
          refine ⟨1707625922703206160837595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276834563604274881116793 1707625922703206160837595)
          ·
            refine ⟨2561438884054809241256393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707625922703206160837595 2561438884054809241256393)
            ·
              refine ⟨1921079163041106930942295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561438884054809241256393 1921079163041106930942295)
              ·
                refine ⟨2881618744561660396413443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921079163041106930942295 2881618744561660396413443)
                ·
                  refine ⟨4322428116842490594620165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881618744561660396413443 4322428116842490594620165)
                  ·
                    refine ⟨810455271907966986491281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4322428116842490594620165 810455271907966986491281)
                    ·
                      refine ⟨607841453930975239868461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810455271907966986491281 607841453930975239868461)
                      ·
                        rfl

theorem cell23_1183767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1183767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183767 prefixEnd_1183767 := by exact prefixLift 1183767
  have htrace : WordTrace (prefixWord ++ tailWord_1183767) baseStart_1183767 baseEnd_1183767 := by
    simpa [prefixWord, tailWord_1183767, baseEnd_1183767] using wordTrace_append hprefix tailTrace_1183767
  have hstable : (prefixWord ++ tailWord_1183767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183767).length < 2 ^ (prefixWord ++ tailWord_1183767).sum := by decide
  have hdescent : baseEnd_1183767 < baseStart_1183767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183773 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 7]
def baseStart_1183773 : Nat := 118140960795 + 1183773 * 2 ^ 59
def prefixEnd_1183773 : Nat := 4983230072969 + 3 ^ 40 * 1183773 * 2
def baseEnd_1183773 : Nat := 67538281646100246265937

theorem tailTrace_1183773 : CollatzResearch.WordTrace tailWord_1183773 prefixEnd_1183773 67538281646100246265937 := by
  unfold tailWord_1183773
  simp only [CollatzResearch.WordTrace]
  refine ⟨43175748340400068177747973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28783832226933378785165315 43175748340400068177747973)
  ·
    refine ⟨8095452813825012783327745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43175748340400068177747973 8095452813825012783327745)
    ·
      refine ⟨6071589610368759587495809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8095452813825012783327745 6071589610368759587495809)
      ·
        refine ⟨4553692207776569690621857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6071589610368759587495809 4553692207776569690621857)
        ·
          refine ⟨3415269155832427267966393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4553692207776569690621857 3415269155832427267966393)
          ·
            refine ⟨2561451866874320450974795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3415269155832427267966393 2561451866874320450974795)
            ·
              refine ⟨3842177800311480676462193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561451866874320450974795 3842177800311480676462193)
              ·
                refine ⟨2881633350233610507346645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842177800311480676462193 2881633350233610507346645)
                ·
                  refine ⟨67538281646100246265937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2881633350233610507346645 67538281646100246265937)
                  ·
                    rfl

theorem cell23_1183773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_1183773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183773 prefixEnd_1183773 := by exact prefixLift 1183773
  have htrace : WordTrace (prefixWord ++ tailWord_1183773) baseStart_1183773 baseEnd_1183773 := by
    simpa [prefixWord, tailWord_1183773, baseEnd_1183773] using wordTrace_append hprefix tailTrace_1183773
  have hstable : (prefixWord ++ tailWord_1183773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183773).length < 2 ^ (prefixWord ++ tailWord_1183773).sum := by decide
  have hdescent : baseEnd_1183773 < baseStart_1183773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183790 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_1183790 : Nat := 118140960795 + 1183790 * 2 ^ 59
def prefixEnd_1183790 : Nat := 4983230072969 + 3 ^ 40 * 1183790 * 2
def baseEnd_1183790 : Nat := 67539251554003183320095

theorem tailTrace_1183790 : CollatzResearch.WordTrace tailWord_1183790 prefixEnd_1183790 67539251554003183320095 := by
  unfold tailWord_1183790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397046047667310010139603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28784245587558986720744549 5397046047667310010139603)
  ·
    refine ⟨8095569071500965015209405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5397046047667310010139603 8095569071500965015209405)
    ·
      refine ⟨3035838401812861880703527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8095569071500965015209405 3035838401812861880703527)
      ·
        refine ⟨4553757602719292821055291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035838401812861880703527 4553757602719292821055291)
        ·
          refine ⟨6830636404078939231582937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4553757602719292821055291 6830636404078939231582937)
          ·
            refine ⟨5122977303059204423687203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6830636404078939231582937 5122977303059204423687203)
            ·
              refine ⟨7684465954588806635530805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122977303059204423687203 7684465954588806635530805)
              ·
                refine ⟨720418683242700622081013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7684465954588806635530805 720418683242700622081013)
                ·
                  refine ⟨67539251554003183320095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 720418683242700622081013 67539251554003183320095)
                  ·
                    rfl

theorem cell23_1183790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_1183790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183790 prefixEnd_1183790 := by exact prefixLift 1183790
  have htrace : WordTrace (prefixWord ++ tailWord_1183790) baseStart_1183790 baseEnd_1183790 := by
    simpa [prefixWord, tailWord_1183790, baseEnd_1183790] using wordTrace_append hprefix tailTrace_1183790
  have hstable : (prefixWord ++ tailWord_1183790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183790).length < 2 ^ (prefixWord ++ tailWord_1183790).sum := by decide
  have hdescent : baseEnd_1183790 < baseStart_1183790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183801 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1183801 : Nat := 118140960795 + 1183801 * 2 ^ 59
def prefixEnd_1183801 : Nat := 4983230072969 + 3 ^ 40 * 1183801 * 2
def baseEnd_1183801 : Nat := 607858912273228106843305

theorem tailTrace_1183801 : CollatzResearch.WordTrace tailWord_1183801 prefixEnd_1183801 607858912273228106843305 := by
  unfold tailWord_1183801
  simp only [CollatzResearch.WordTrace]
  refine ⟨43176769584298628959767257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28784513056199085973178171 43176769584298628959767257)
  ·
    refine ⟨32382577188223971719825443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43176769584298628959767257 32382577188223971719825443)
    ·
      refine ⟨48573865782335957579738165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32382577188223971719825443 48573865782335957579738165)
      ·
        refine ⟨4553799917093996023100453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48573865782335957579738165 4553799917093996023100453)
        ·
          refine ⟨853837484455124254331335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4553799917093996023100453 853837484455124254331335)
          ·
            refine ⟨1280756226682686381497003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853837484455124254331335 1280756226682686381497003)
            ·
              refine ⟨1921134340024029572245505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280756226682686381497003 1921134340024029572245505)
              ·
                refine ⟨1440850755018022179184129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921134340024029572245505 1440850755018022179184129)
                ·
                  refine ⟨1080638066263516634388097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1440850755018022179184129 1080638066263516634388097)
                  ·
                    refine ⟨810478549697637475791073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1080638066263516634388097 810478549697637475791073)
                    ·
                      refine ⟨607858912273228106843305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 810478549697637475791073 607858912273228106843305)
                      ·
                        rfl

theorem cell23_1183801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1183801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183801 prefixEnd_1183801 := by exact prefixLift 1183801
  have htrace : WordTrace (prefixWord ++ tailWord_1183801) baseStart_1183801 baseEnd_1183801 := by
    simpa [prefixWord, tailWord_1183801, baseEnd_1183801] using wordTrace_append hprefix tailTrace_1183801
  have hstable : (prefixWord ++ tailWord_1183801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183801).length < 2 ^ (prefixWord ++ tailWord_1183801).sum := by decide
  have hdescent : baseEnd_1183801 < baseStart_1183801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183833 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_1183833 : Nat := 118140960795 + 1183833 * 2 ^ 59
def prefixEnd_1183833 : Nat := 4983230072969 + 3 ^ 40 * 1183833 * 2
def baseEnd_1183833 : Nat := 202625114551390660547719

theorem tailTrace_1183833 : CollatzResearch.WordTrace tailWord_1183833 prefixEnd_1183833 202625114551390660547719 := by
  unfold tailWord_1183833
  simp only [CollatzResearch.WordTrace]
  refine ⟨43177936720182698424932153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28785291146788465616621435 43177936720182698424932153)
  ·
    refine ⟨32383452540137023818699115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43177936720182698424932153 32383452540137023818699115)
    ·
      refine ⟨48575178810205535728048673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32383452540137023818699115 48575178810205535728048673)
      ·
        refine ⟨36431384107654151796036505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48575178810205535728048673 36431384107654151796036505)
        ·
          refine ⟨27323538080740613847027379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36431384107654151796036505 27323538080740613847027379)
          ·
            refine ⟨40985307121110920770541069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27323538080740613847027379 40985307121110920770541069)
            ·
              refine ⟨15369490170416595288952901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40985307121110920770541069 15369490170416595288952901)
              ·
                refine ⟨2881779406953111616678669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15369490170416595288952901 2881779406953111616678669)
                ·
                  refine ⟨1080667277607416856254501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2881779406953111616678669 1080667277607416856254501)
                  ·
                    refine ⟨202625114551390660547719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080667277607416856254501 202625114551390660547719)
                    ·
                      rfl

theorem cell23_1183833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_1183833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183833 prefixEnd_1183833 := by exact prefixLift 1183833
  have htrace : WordTrace (prefixWord ++ tailWord_1183833) baseStart_1183833 baseEnd_1183833 := by
    simpa [prefixWord, tailWord_1183833, baseEnd_1183833] using wordTrace_append hprefix tailTrace_1183833
  have hstable : (prefixWord ++ tailWord_1183833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183833).length < 2 ^ (prefixWord ++ tailWord_1183833).sum := by decide
  have hdescent : baseEnd_1183833 < baseStart_1183833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183843 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1183843 : Nat := 118140960795 + 1183843 * 2 ^ 59
def prefixEnd_1183843 : Nat := 4983230072969 + 3 ^ 40 * 1183843 * 2
def baseEnd_1183843 : Nat := 607880478460716942518111

theorem tailTrace_1183843 : CollatzResearch.WordTrace tailWord_1183843 prefixEnd_1183843 607880478460716942518111 := by
  unfold tailWord_1183843
  simp only [CollatzResearch.WordTrace]
  refine ⟨43178301450146470132796183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28785534300097646755197455 43178301450146470132796183)
  ·
    refine ⟨64767452175219705199194275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43178301450146470132796183 64767452175219705199194275)
    ·
      refine ⟨97151178262829557798791413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64767452175219705199194275 97151178262829557798791413)
      ·
        refine ⟨9107922962140271043636695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97151178262829557798791413 9107922962140271043636695)
        ·
          refine ⟨13661884443210406565455043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9107922962140271043636695 13661884443210406565455043)
          ·
            refine ⟨20492826664815609848182565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13661884443210406565455043 20492826664815609848182565)
            ·
              refine ⟨3842404999652926846534231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20492826664815609848182565 3842404999652926846534231)
              ·
                refine ⟨5763607499479390269801347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842404999652926846534231 5763607499479390269801347)
                ·
                  refine ⟨8645411249219085404702021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763607499479390269801347 8645411249219085404702021)
                  ·
                    refine ⟨1621014609228578513381629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8645411249219085404702021 1621014609228578513381629)
                    ·
                      refine ⟨607880478460716942518111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1621014609228578513381629 607880478460716942518111)
                      ·
                        rfl

theorem cell23_1183843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1183843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183843 prefixEnd_1183843 := by exact prefixLift 1183843
  have htrace : WordTrace (prefixWord ++ tailWord_1183843) baseStart_1183843 baseEnd_1183843 := by
    simpa [prefixWord, tailWord_1183843, baseEnd_1183843] using wordTrace_append hprefix tailTrace_1183843
  have hstable : (prefixWord ++ tailWord_1183843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183843).length < 2 ^ (prefixWord ++ tailWord_1183843).sum := by decide
  have hdescent : baseEnd_1183843 < baseStart_1183843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183880 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 6]
def baseStart_1183880 : Nat := 118140960795 + 1183880 * 2 ^ 59
def prefixEnd_1183880 : Nat := 4983230072969 + 3 ^ 40 * 1183880 * 2
def baseEnd_1183880 : Nat := 67544386360548144195049

theorem tailTrace_1183880 : CollatzResearch.WordTrace tailWord_1183880 prefixEnd_1183880 67544386360548144195049 := by
  unfold tailWord_1183880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21589825475506212725946547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28786433967341616967928729 21589825475506212725946547)
  ·
    refine ⟨32384738213259319088919821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21589825475506212725946547 32384738213259319088919821)
    ·
      refine ⟨12144276829972244658344933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32384738213259319088919821 12144276829972244658344933)
      ·
        refine ⟨2277051905619795873439675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12144276829972244658344933 2277051905619795873439675)
        ·
          refine ⟨3415577858429693810159513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277051905619795873439675 3415577858429693810159513)
          ·
            refine ⟨2561683393822270357619635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3415577858429693810159513 2561683393822270357619635)
            ·
              refine ⟨3842525090733405536429453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561683393822270357619635 3842525090733405536429453)
              ·
                refine ⟨1440946909025027076161045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3842525090733405536429453 1440946909025027076161045)
                ·
                  refine ⟨67544386360548144195049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1440946909025027076161045 67544386360548144195049)
                  ·
                    rfl

theorem cell23_1183880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_1183880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183880 prefixEnd_1183880 := by exact prefixLift 1183880
  have htrace : WordTrace (prefixWord ++ tailWord_1183880) baseStart_1183880 baseEnd_1183880 := by
    simpa [prefixWord, tailWord_1183880, baseEnd_1183880] using wordTrace_append hprefix tailTrace_1183880
  have hstable : (prefixWord ++ tailWord_1183880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183880).length < 2 ^ (prefixWord ++ tailWord_1183880).sum := by decide
  have hdescent : baseEnd_1183880 < baseStart_1183880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183893 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1183893 : Nat := 118140960795 + 1183893 * 2 ^ 59
def prefixEnd_1183893 : Nat := 4983230072969 + 3 ^ 40 * 1183893 * 2
def baseEnd_1183893 : Nat := 202635384164480582297627

theorem tailTrace_1183893 : CollatzResearch.WordTrace tailWord_1183893 prefixEnd_1183893 202635384164480582297627 := by
  unfold tailWord_1183893
  simp only [CollatzResearch.WordTrace]
  refine ⟨43180125099965328672116333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28786750066643552448077555 43180125099965328672116333)
  ·
    refine ⟨16192546912486998252043625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43180125099965328672116333 16192546912486998252043625)
    ·
      refine ⟨12144410184365248689032719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16192546912486998252043625 12144410184365248689032719)
      ·
        refine ⟨18216615276547873033549079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12144410184365248689032719 18216615276547873033549079)
        ·
          refine ⟨27324922914821809550323619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18216615276547873033549079 27324922914821809550323619)
          ·
            refine ⟨40987384372232714325485429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27324922914821809550323619 40987384372232714325485429)
            ·
              refine ⟨3842567284896816968014259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40987384372232714325485429 3842567284896816968014259)
              ·
                refine ⟨5763850927345225452021389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842567284896816968014259 5763850927345225452021389)
                ·
                  refine ⟨2161444097754459544508021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5763850927345225452021389 2161444097754459544508021)
                  ·
                    refine ⟨202635384164480582297627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2161444097754459544508021 202635384164480582297627)
                    ·
                      rfl

theorem cell23_1183893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1183893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183893 prefixEnd_1183893 := by exact prefixLift 1183893
  have htrace : WordTrace (prefixWord ++ tailWord_1183893) baseStart_1183893 baseEnd_1183893 := by
    simpa [prefixWord, tailWord_1183893, baseEnd_1183893] using wordTrace_append hprefix tailTrace_1183893
  have hstable : (prefixWord ++ tailWord_1183893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183893).length < 2 ^ (prefixWord ++ tailWord_1183893).sum := by decide
  have hdescent : baseEnd_1183893 < baseStart_1183893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1183933 : Nat := 118140960795 + 1183933 * 2 ^ 59
def prefixEnd_1183933 : Nat := 4983230072969 + 3 ^ 40 * 1183933 * 2
def baseEnd_1183933 : Nat := 607926691719621590392697

theorem tailTrace_1183933 : CollatzResearch.WordTrace tailWord_1183933 prefixEnd_1183933 607926691719621590392697 := by
  unfold tailWord_1183933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43181584019820415503572453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28787722679880277002381635 43181584019820415503572453)
  ·
    refine ⟨8096547003716327906919835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43181584019820415503572453 8096547003716327906919835)
    ·
      refine ⟨12144820505574491860379753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8096547003716327906919835 12144820505574491860379753)
      ·
        refine ⟨9108615379180868895284815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12144820505574491860379753 9108615379180868895284815)
        ·
          refine ⟨13662923068771303342927223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108615379180868895284815 13662923068771303342927223)
          ·
            refine ⟨20494384603156955014390835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13662923068771303342927223 20494384603156955014390835)
            ·
              refine ⟨30741576904735432521586253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20494384603156955014390835 30741576904735432521586253)
              ·
                refine ⟨11528091339275787195594845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30741576904735432521586253 11528091339275787195594845)
                ·
                  refine ⟨4323034252228420198348067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11528091339275787195594845 4323034252228420198348067)
                  ·
                    refine ⟨6484551378342630297522101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323034252228420198348067 6484551378342630297522101)
                    ·
                      refine ⟨607926691719621590392697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6484551378342630297522101 607926691719621590392697)
                      ·
                        rfl

theorem cell23_1183933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1183933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1183933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1183933 prefixEnd_1183933 := by exact prefixLift 1183933
  have htrace : WordTrace (prefixWord ++ tailWord_1183933) baseStart_1183933 baseEnd_1183933 := by
    simpa [prefixWord, tailWord_1183933, baseEnd_1183933] using wordTrace_append hprefix tailTrace_1183933
  have hstable : (prefixWord ++ tailWord_1183933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183933).length < 2 ^ (prefixWord ++ tailWord_1183933).sum := by decide
  have hdescent : baseEnd_1183933 < baseStart_1183933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
