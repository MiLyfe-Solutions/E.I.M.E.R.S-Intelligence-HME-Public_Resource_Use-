import V185TrunkScan23Chunk0079

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_474953 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 5, 2, 2]
def baseStart_474953 : Nat := 118140960795 + 474953 * 2 ^ 59
def prefixEnd_474953 : Nat := 4983230072969 + 3 ^ 40 * 474953 * 2
def baseEnd_474953 : Nat := 243879177294985477903237

theorem tailTrace_474953 : CollatzResearch.WordTrace tailWord_474953 prefixEnd_474953 243879177294985477903237 := by
  unfold tailWord_474953
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322959048333871359573513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548639365555914239715675 17322959048333871359573513)
  ·
    refine ⟨12992219286250403519680135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17322959048333871359573513 12992219286250403519680135)
    ·
      refine ⟨19488328929375605279520203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992219286250403519680135 19488328929375605279520203)
      ·
        refine ⟨29232493394063407919280305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488328929375605279520203 29232493394063407919280305)
        ·
          refine ⟨21924370045547555939460229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29232493394063407919280305 21924370045547555939460229)
          ·
            refine ⟨4110819383540166738648793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21924370045547555939460229 4110819383540166738648793)
            ·
              refine ⟨3083114537655125053986595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110819383540166738648793 3083114537655125053986595)
              ·
                refine ⟨4624671806482687580979893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083114537655125053986595 4624671806482687580979893)
                ·
                  refine ⟨433562981857751960716865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624671806482687580979893 433562981857751960716865)
                  ·
                    refine ⟨325172236393313970537649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433562981857751960716865 325172236393313970537649)
                    ·
                      refine ⟨243879177294985477903237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325172236393313970537649 243879177294985477903237)
                      ·
                        rfl

theorem cell23_474953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2, 2].length) (baseStart_474953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474953 prefixEnd_474953 := by exact prefixLift 474953
  have htrace : WordTrace (prefixWord ++ tailWord_474953) baseStart_474953 baseEnd_474953 := by
    simpa [prefixWord, tailWord_474953, baseEnd_474953] using wordTrace_append hprefix tailTrace_474953
  have hstable : (prefixWord ++ tailWord_474953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474953).length < 2 ^ (prefixWord ++ tailWord_474953).sum := by decide
  have hdescent : baseEnd_474953 < baseStart_474953 := by decide
  rcases family_descends (prefixWord ++ tailWord_474953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474957 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_474957 : Nat := 118140960795 + 474957 * 2 ^ 59
def prefixEnd_474957 : Nat := 4983230072969 + 3 ^ 40 * 474957 * 2
def baseEnd_474957 : Nat := 243881231217603462253219

theorem tailTrace_474957 : CollatzResearch.WordTrace tailWord_474957 prefixEnd_474957 243881231217603462253219 := by
  unfold tailWord_474957
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323104940319380042719125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548736626879586695146083 17323104940319380042719125)
  ·
    refine ⟨812020544077470939502459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17323104940319380042719125 812020544077470939502459)
    ·
      refine ⟨1218030816116206409253689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812020544077470939502459 1218030816116206409253689)
      ·
        refine ⟨913523112087154806940267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1218030816116206409253689 913523112087154806940267)
        ·
          refine ⟨1370284668130732210410401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913523112087154806940267 1370284668130732210410401)
          ·
            refine ⟨1027713501098049157807801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370284668130732210410401 1027713501098049157807801)
            ·
              refine ⟨770785125823536868355851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027713501098049157807801 770785125823536868355851)
              ·
                refine ⟨1156177688735305302533777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770785125823536868355851 1156177688735305302533777)
                ·
                  refine ⟨867133266551478976900333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156177688735305302533777 867133266551478976900333)
                  ·
                    refine ⟨325174974956804616337625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867133266551478976900333 325174974956804616337625)
                    ·
                      refine ⟨243881231217603462253219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325174974956804616337625 243881231217603462253219)
                      ·
                        rfl

theorem cell23_474957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_474957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474957 prefixEnd_474957 := by exact prefixLift 474957
  have htrace : WordTrace (prefixWord ++ tailWord_474957) baseStart_474957 baseEnd_474957 := by
    simpa [prefixWord, tailWord_474957, baseEnd_474957] using wordTrace_append hprefix tailTrace_474957
  have hstable : (prefixWord ++ tailWord_474957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474957).length < 2 ^ (prefixWord ++ tailWord_474957).sum := by decide
  have hdescent : baseEnd_474957 < baseStart_474957 := by decide
  rcases family_descends (prefixWord ++ tailWord_474957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474980 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_474980 : Nat := 118140960795 + 474980 * 2 ^ 59
def prefixEnd_474980 : Nat := 4983230072969 + 3 ^ 40 * 474980 * 2
def baseEnd_474980 : Nat := 81297680424218957421871

theorem tailTrace_474980 : CollatzResearch.WordTrace tailWord_474980 prefixEnd_474980 81297680424218957421871 := by
  unfold tailWord_474980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8661971909618027485403197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11549295879490703313870929 8661971909618027485403197)
  ·
    refine ⟨3248239466106760307026199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8661971909618027485403197 3248239466106760307026199)
    ·
      refine ⟨4872359199160140460539299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3248239466106760307026199 4872359199160140460539299)
      ·
        refine ⟨7308538798740210690808949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872359199160140460539299 7308538798740210690808949)
        ·
          refine ⟨685175512381894752263339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7308538798740210690808949 685175512381894752263339)
          ·
            refine ⟨1027763268572842128395009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685175512381894752263339 1027763268572842128395009)
            ·
              refine ⟨770822451429631596296257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027763268572842128395009 770822451429631596296257)
              ·
                refine ⟨578116838572223697222193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770822451429631596296257 578116838572223697222193)
                ·
                  refine ⟨433587628929167772916645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578116838572223697222193 433587628929167772916645)
                  ·
                    refine ⟨81297680424218957421871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433587628929167772916645 81297680424218957421871)
                    ·
                      rfl

theorem cell23_474980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_474980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474980 prefixEnd_474980 := by exact prefixLift 474980
  have htrace : WordTrace (prefixWord ++ tailWord_474980) baseStart_474980 baseEnd_474980 := by
    simpa [prefixWord, tailWord_474980, baseEnd_474980] using wordTrace_append hprefix tailTrace_474980
  have hstable : (prefixWord ++ tailWord_474980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474980).length < 2 ^ (prefixWord ++ tailWord_474980).sum := by decide
  have hdescent : baseEnd_474980 < baseStart_474980 := by decide
  rcases family_descends (prefixWord ++ tailWord_474980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474999 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_474999 : Nat := 118140960795 + 474999 * 2 ^ 59
def prefixEnd_474999 : Nat := 4983230072969 + 3 ^ 40 * 474999 * 2
def baseEnd_474999 : Nat := 243902797405092297928025

theorem tailTrace_474999 : CollatzResearch.WordTrace tailWord_474999 prefixEnd_474999 243902797405092297928025 := by
  unfold tailWord_474999
  simp only [CollatzResearch.WordTrace]
  refine ⟨17324636806167221215748051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11549757870778147477165367 17324636806167221215748051)
  ·
    refine ⟨25986955209250831823622077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17324636806167221215748051 25986955209250831823622077)
    ·
      refine ⟨9745108203469061933858279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25986955209250831823622077 9745108203469061933858279)
      ·
        refine ⟨14617662305203592900787419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745108203469061933858279 14617662305203592900787419)
        ·
          refine ⟨21926493457805389351181129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14617662305203592900787419 21926493457805389351181129)
          ·
            refine ⟨16444870093354042013385847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21926493457805389351181129 16444870093354042013385847)
            ·
              refine ⟨24667305140031063020078771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16444870093354042013385847 24667305140031063020078771)
              ·
                refine ⟨37000957710046594530118157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24667305140031063020078771 37000957710046594530118157)
                ·
                  refine ⟨13875359141267472948794309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37000957710046594530118157 13875359141267472948794309)
                  ·
                    refine ⟨2601629838987651177898933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13875359141267472948794309 2601629838987651177898933)
                    ·
                      refine ⟨243902797405092297928025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2601629838987651177898933 243902797405092297928025)
                      ·
                        rfl

theorem cell23_474999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_474999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_474999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_474999 prefixEnd_474999 := by exact prefixLift 474999
  have htrace : WordTrace (prefixWord ++ tailWord_474999) baseStart_474999 baseEnd_474999 := by
    simpa [prefixWord, tailWord_474999, baseEnd_474999] using wordTrace_append hprefix tailTrace_474999
  have hstable : (prefixWord ++ tailWord_474999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474999).length < 2 ^ (prefixWord ++ tailWord_474999).sum := by decide
  have hdescent : baseEnd_474999 < baseStart_474999 := by decide
  rcases family_descends (prefixWord ++ tailWord_474999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475013 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_475013 : Nat := 118140960795 + 475013 * 2 ^ 59
def prefixEnd_475013 : Nat := 4983230072969 + 3 ^ 40 * 475013 * 2
def baseEnd_475013 : Nat := 243909986134255243152961

theorem tailTrace_475013 : CollatzResearch.WordTrace tailWord_475013 prefixEnd_475013 243909986134255243152961 := by
  unfold tailWord_475013
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325147428116501606757693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11550098285411001071171795 17325147428116501606757693)
  ·
    refine ⟨6496930285543688102534135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17325147428116501606757693 6496930285543688102534135)
    ·
      refine ⟨9745395428315532153801203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496930285543688102534135 9745395428315532153801203)
      ·
        refine ⟨14618093142473298230701805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745395428315532153801203 14618093142473298230701805)
        ·
          refine ⟨5481784928427486836513177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14618093142473298230701805 5481784928427486836513177)
          ·
            refine ⟨4111338696320615127384883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481784928427486836513177 4111338696320615127384883)
            ·
              refine ⟨6167008044480922691077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111338696320615127384883 6167008044480922691077325)
              ·
                refine ⟨2312628016680346009153997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6167008044480922691077325 2312628016680346009153997)
                ·
                  refine ⟨867235506255129753432749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2312628016680346009153997 867235506255129753432749)
                  ·
                    refine ⟨325213314845673657537281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867235506255129753432749 325213314845673657537281)
                    ·
                      refine ⟨243909986134255243152961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325213314845673657537281 243909986134255243152961)
                      ·
                        rfl

theorem cell23_475013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_475013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475013 prefixEnd_475013 := by exact prefixLift 475013
  have htrace : WordTrace (prefixWord ++ tailWord_475013) baseStart_475013 baseEnd_475013 := by
    simpa [prefixWord, tailWord_475013, baseEnd_475013] using wordTrace_append hprefix tailTrace_475013
  have hstable : (prefixWord ++ tailWord_475013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475013).length < 2 ^ (prefixWord ++ tailWord_475013).sum := by decide
  have hdescent : baseEnd_475013 < baseStart_475013 := by decide
  rcases family_descends (prefixWord ++ tailWord_475013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475019 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 8]
def baseStart_475019 : Nat := 118140960795 + 475019 * 2 ^ 59
def prefixEnd_475019 : Nat := 4983230072969 + 3 ^ 40 * 475019 * 2
def baseEnd_475019 : Nat := 81304355672727406559311

theorem tailTrace_475019 : CollatzResearch.WordTrace tailWord_475019 prefixEnd_475019 81304355672727406559311 := by
  unfold tailWord_475019
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325366266094764631476111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11550244177396509754317407 17325366266094764631476111)
  ·
    refine ⟨25988049399142146947214167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325366266094764631476111 25988049399142146947214167)
    ·
      refine ⟨38982074098713220420821251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988049399142146947214167 38982074098713220420821251)
      ·
        refine ⟨58473111148069830631231877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982074098713220420821251 58473111148069830631231877)
        ·
          refine ⟨10963708340263093243355977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58473111148069830631231877 10963708340263093243355977)
          ·
            refine ⟨8222781255197319932516983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963708340263093243355977 8222781255197319932516983)
            ·
              refine ⟨12334171882795979898775475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8222781255197319932516983 12334171882795979898775475)
              ·
                refine ⟨18501257824193969848163213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12334171882795979898775475 18501257824193969848163213)
                ·
                  refine ⟨6937971684072738693061205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18501257824193969848163213 6937971684072738693061205)
                  ·
                    refine ⟨81304355672727406559311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6937971684072738693061205 81304355672727406559311)
                    ·
                      rfl

theorem cell23_475019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_475019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475019 prefixEnd_475019 := by exact prefixLift 475019
  have htrace : WordTrace (prefixWord ++ tailWord_475019) baseStart_475019 baseEnd_475019 := by
    simpa [prefixWord, tailWord_475019, baseEnd_475019] using wordTrace_append hprefix tailTrace_475019
  have hstable : (prefixWord ++ tailWord_475019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475019).length < 2 ^ (prefixWord ++ tailWord_475019).sum := by decide
  have hdescent : baseEnd_475019 < baseStart_475019 := by decide
  rcases family_descends (prefixWord ++ tailWord_475019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475037 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_475037 : Nat := 118140960795 + 475037 * 2 ^ 59
def prefixEnd_475037 : Nat := 4983230072969 + 3 ^ 40 * 475037 * 2
def baseEnd_475037 : Nat := 243922309669963149252851

theorem tailTrace_475037 : CollatzResearch.WordTrace tailWord_475037 prefixEnd_475037 243922309669963149252851 := by
  unfold tailWord_475037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326022780029553705631365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11550681853353035803754243 17326022780029553705631365)
  ·
    refine ⟨3248629271255541319805881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17326022780029553705631365 3248629271255541319805881)
    ·
      refine ⟨2436471953441655989854411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3248629271255541319805881 2436471953441655989854411)
      ·
        refine ⟨3654707930162483984781617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436471953441655989854411 3654707930162483984781617)
        ·
          refine ⟨2741030947621862988586213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3654707930162483984781617 2741030947621862988586213)
          ·
            refine ⟨513943302679099310359915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2741030947621862988586213 513943302679099310359915)
            ·
              refine ⟨770914954018648965539873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513943302679099310359915 770914954018648965539873)
              ·
                refine ⟨578186215513986724154905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770914954018648965539873 578186215513986724154905)
                ·
                  refine ⟨433639661635490043116179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578186215513986724154905 433639661635490043116179)
                  ·
                    refine ⟨650459492453235064674269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433639661635490043116179 650459492453235064674269)
                    ·
                      refine ⟨243922309669963149252851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650459492453235064674269 243922309669963149252851)
                      ·
                        rfl

theorem cell23_475037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_475037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475037 prefixEnd_475037 := by exact prefixLift 475037
  have htrace : WordTrace (prefixWord ++ tailWord_475037) baseStart_475037 baseEnd_475037 := by
    simpa [prefixWord, tailWord_475037, baseEnd_475037] using wordTrace_append hprefix tailTrace_475037
  have hstable : (prefixWord ++ tailWord_475037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475037).length < 2 ^ (prefixWord ++ tailWord_475037).sum := by decide
  have hdescent : baseEnd_475037 < baseStart_475037 := by decide
  rcases family_descends (prefixWord ++ tailWord_475037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475111 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_475111 : Nat := 118140960795 + 475111 * 2 ^ 59
def prefixEnd_475111 : Nat := 4983230072969 + 3 ^ 40 * 475111 * 2
def baseEnd_475111 : Nat := 243960307238395859727511

theorem tailTrace_475111 : CollatzResearch.WordTrace tailWord_475111 prefixEnd_475111 243960307238395859727511 := by
  unfold tailWord_475111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17328721781761464343825187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11552481187840976229216791 17328721781761464343825187)
  ·
    refine ⟨25993082672642196515737781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17328721781761464343825187 25993082672642196515737781)
    ·
      refine ⟨2436851500560205923350417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25993082672642196515737781 2436851500560205923350417)
      ·
        refine ⟨1827638625420154442512813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436851500560205923350417 1827638625420154442512813)
        ·
          refine ⟨685364484532557915942305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1827638625420154442512813 685364484532557915942305)
          ·
            refine ⟨514023363399418436956729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685364484532557915942305 514023363399418436956729)
            ·
              refine ⟨385517522549563827717547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514023363399418436956729 385517522549563827717547)
              ·
                refine ⟨578276283824345741576321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385517522549563827717547 578276283824345741576321)
                ·
                  refine ⟨433707212868259306182241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578276283824345741576321 433707212868259306182241)
                  ·
                    refine ⟨325280409651194479636681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433707212868259306182241 325280409651194479636681)
                    ·
                      refine ⟨243960307238395859727511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325280409651194479636681 243960307238395859727511)
                      ·
                        rfl

theorem cell23_475111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_475111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475111 prefixEnd_475111 := by exact prefixLift 475111
  have htrace : WordTrace (prefixWord ++ tailWord_475111) baseStart_475111 baseEnd_475111 := by
    simpa [prefixWord, tailWord_475111, baseEnd_475111] using wordTrace_append hprefix tailTrace_475111
  have hstable : (prefixWord ++ tailWord_475111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475111).length < 2 ^ (prefixWord ++ tailWord_475111).sum := by decide
  have hdescent : baseEnd_475111 < baseStart_475111 := by decide
  rcases family_descends (prefixWord ++ tailWord_475111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475116 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_475116 : Nat := 118140960795 + 475116 * 2 ^ 59
def prefixEnd_475116 : Nat := 4983230072969 + 3 ^ 40 * 475116 * 2
def baseEnd_475116 : Nat := 243962874641668340164987

theorem tailTrace_475116 : CollatzResearch.WordTrace tailWord_475116 prefixEnd_475116 243962874641668340164987 := by
  unfold tailWord_475116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664452073371675098878601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11552602764495566798504801 8664452073371675098878601)
  ·
    refine ⟨6498339055028756324158951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8664452073371675098878601 6498339055028756324158951)
    ·
      refine ⟨9747508582543134486238427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498339055028756324158951 9747508582543134486238427)
      ·
        refine ⟨14621262873814701729357641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747508582543134486238427 14621262873814701729357641)
        ·
          refine ⟨10965947155361026297018231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14621262873814701729357641 10965947155361026297018231)
          ·
            refine ⟨16448920733041539445527347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10965947155361026297018231 16448920733041539445527347)
            ·
              refine ⟨24673381099562309168291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16448920733041539445527347 24673381099562309168291021)
              ·
                refine ⟨9252517912335865938109133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24673381099562309168291021 9252517912335865938109133)
                ·
                  refine ⟨3469694217125949726790925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9252517912335865938109133 3469694217125949726790925)
                  ·
                    refine ⟨1301135331422231147546597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469694217125949726790925 1301135331422231147546597)
                    ·
                      refine ⟨243962874641668340164987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1301135331422231147546597 243962874641668340164987)
                      ·
                        rfl

theorem cell23_475116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_475116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475116 prefixEnd_475116 := by exact prefixLift 475116
  have htrace : WordTrace (prefixWord ++ tailWord_475116) baseStart_475116 baseEnd_475116 := by
    simpa [prefixWord, tailWord_475116, baseEnd_475116] using wordTrace_append hprefix tailTrace_475116
  have hstable : (prefixWord ++ tailWord_475116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475116).length < 2 ^ (prefixWord ++ tailWord_475116).sum := by decide
  have hdescent : baseEnd_475116 < baseStart_475116 := by decide
  rcases family_descends (prefixWord ++ tailWord_475116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475133 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_475133 : Nat := 118140960795 + 475133 * 2 ^ 59
def prefixEnd_475133 : Nat := 4983230072969 + 3 ^ 40 * 475133 * 2
def baseEnd_475133 : Nat := 243971603812794773652409

theorem tailTrace_475133 : CollatzResearch.WordTrace tailWord_475133 prefixEnd_475133 243971603812794773652409 := by
  unfold tailWord_475133
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329524187681762101126053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11553016125121174734084035 17329524187681762101126053)
  ·
    refine ⟨3249285785190330393961135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17329524187681762101126053 3249285785190330393961135)
    ·
      refine ⟨4873928677785495590941703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249285785190330393961135 4873928677785495590941703)
      ·
        refine ⟨7310893016678243386412555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873928677785495590941703 7310893016678243386412555)
        ·
          refine ⟨10966339525017365079618833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310893016678243386412555 10966339525017365079618833)
          ·
            refine ⟨8224754643763023809714125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10966339525017365079618833 8224754643763023809714125)
            ·
              refine ⟨3084282991411133928642797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8224754643763023809714125 3084282991411133928642797)
              ·
                refine ⟨1156606121779175223241049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084282991411133928642797 1156606121779175223241049)
                ·
                  refine ⟨867454591334381417430787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156606121779175223241049 867454591334381417430787)
                  ·
                    refine ⟨1301181887001572126146181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 867454591334381417430787 1301181887001572126146181)
                    ·
                      refine ⟨243971603812794773652409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1301181887001572126146181 243971603812794773652409)
                      ·
                        rfl

theorem cell23_475133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_475133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475133 prefixEnd_475133 := by exact prefixLift 475133
  have htrace : WordTrace (prefixWord ++ tailWord_475133) baseStart_475133 baseEnd_475133 := by
    simpa [prefixWord, tailWord_475133, baseEnd_475133] using wordTrace_append hprefix tailTrace_475133
  have hstable : (prefixWord ++ tailWord_475133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475133).length < 2 ^ (prefixWord ++ tailWord_475133).sum := by decide
  have hdescent : baseEnd_475133 < baseStart_475133 := by decide
  rcases family_descends (prefixWord ++ tailWord_475133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475150 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_475150 : Nat := 118140960795 + 475150 * 2 ^ 59
def prefixEnd_475150 : Nat := 4983230072969 + 3 ^ 40 * 475150 * 2
def baseEnd_475150 : Nat := 243980332983921207139831

theorem tailTrace_475150 : CollatzResearch.WordTrace tailWord_475150 prefixEnd_475150 243980332983921207139831 := by
  unfold tailWord_475150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166268028577521750561863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11553429485746782669663269 2166268028577521750561863)
  ·
    refine ⟨3249402042866282625842795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166268028577521750561863 3249402042866282625842795)
    ·
      refine ⟨4874103064299423938764193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249402042866282625842795 4874103064299423938764193)
      ·
        refine ⟨3655577298224567954073145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4874103064299423938764193 3655577298224567954073145)
        ·
          refine ⟨2741682973668425965554859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3655577298224567954073145 2741682973668425965554859)
          ·
            refine ⟨4112524460502638948332289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741682973668425965554859 4112524460502638948332289)
            ·
              refine ⟨3084393345376979211249217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112524460502638948332289 3084393345376979211249217)
              ·
                refine ⟨2313295009032734408436913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084393345376979211249217 2313295009032734408436913)
                ·
                  refine ⟨1734971256774550806327685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313295009032734408436913 1734971256774550806327685)
                  ·
                    refine ⟨325307110645228276186441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1734971256774550806327685 325307110645228276186441)
                    ·
                      refine ⟨243980332983921207139831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325307110645228276186441 243980332983921207139831)
                      ·
                        rfl

theorem cell23_475150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_475150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475150 prefixEnd_475150 := by exact prefixLift 475150
  have htrace : WordTrace (prefixWord ++ tailWord_475150) baseStart_475150 baseEnd_475150 := by
    simpa [prefixWord, tailWord_475150, baseEnd_475150] using wordTrace_append hprefix tailTrace_475150
  have hstable : (prefixWord ++ tailWord_475150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475150).length < 2 ^ (prefixWord ++ tailWord_475150).sum := by decide
  have hdescent : baseEnd_475150 < baseStart_475150 := by decide
  rcases family_descends (prefixWord ++ tailWord_475150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475173 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 6]
def baseStart_475173 : Nat := 118140960795 + 475173 * 2 ^ 59
def prefixEnd_475173 : Nat := 4983230072969 + 3 ^ 40 * 475173 * 2
def baseEnd_475173 : Nat := 27110238115441624128025

theorem tailTrace_475173 : CollatzResearch.WordTrace tailWord_475173 prefixEnd_475173 27110238115441624128025 := by
  unfold tailWord_475173
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330983107536848932582173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11553988738357899288388115 17330983107536848932582173)
  ·
    refine ⟨6499118665326318349718315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17330983107536848932582173 6499118665326318349718315)
    ·
      refine ⟨9748677997989477524577473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499118665326318349718315 9748677997989477524577473)
      ·
        refine ⟨7311508498492108143433105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9748677997989477524577473 7311508498492108143433105)
        ·
          refine ⟨5483631373869081107574829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7311508498492108143433105 5483631373869081107574829)
          ·
            refine ⟨2056361765200905415340561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5483631373869081107574829 2056361765200905415340561)
            ·
              refine ⟨1542271323900679061505421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056361765200905415340561 1542271323900679061505421)
              ·
                refine ⟨578351746462754648064533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1542271323900679061505421 578351746462754648064533)
                ·
                  refine ⟨27110238115441624128025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 578351746462754648064533 27110238115441624128025)
                  ·
                    rfl

theorem cell23_475173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_475173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475173 prefixEnd_475173 := by exact prefixLift 475173
  have htrace : WordTrace (prefixWord ++ tailWord_475173) baseStart_475173 baseEnd_475173 := by
    simpa [prefixWord, tailWord_475173, baseEnd_475173] using wordTrace_append hprefix tailTrace_475173
  have hstable : (prefixWord ++ tailWord_475173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475173).length < 2 ^ (prefixWord ++ tailWord_475173).sum := by decide
  have hdescent : baseEnd_475173 < baseStart_475173 := by decide
  rcases family_descends (prefixWord ++ tailWord_475173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475210 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2]
def baseStart_475210 : Nat := 118140960795 + 475210 * 2 ^ 59
def prefixEnd_475210 : Nat := 4983230072969 + 3 ^ 40 * 475210 * 2
def baseEnd_475210 : Nat := 244011141823190972389555

theorem tailTrace_475210 : CollatzResearch.WordTrace tailWord_475210 prefixEnd_475210 244011141823190972389555 := by
  unfold tailWord_475210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333083152100701062919771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11554888405601869501119389 4333083152100701062919771)
  ·
    refine ⟨6499624728151051594379657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333083152100701062919771 6499624728151051594379657)
    ·
      refine ⟨4874718546113288695784743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6499624728151051594379657 4874718546113288695784743)
      ·
        refine ⟨7312077819169933043677115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874718546113288695784743 7312077819169933043677115)
        ·
          refine ⟨10968116728754899565515673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312077819169933043677115 10968116728754899565515673)
          ·
            refine ⟨8226087546566174674136755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10968116728754899565515673 8226087546566174674136755)
            ·
              refine ⟨12339131319849262011205133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226087546566174674136755 12339131319849262011205133)
              ·
                refine ⟨4627174244943473254201925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12339131319849262011205133 4627174244943473254201925)
                ·
                  refine ⟨867595170926901235162861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4627174244943473254201925 867595170926901235162861)
                  ·
                    refine ⟨325348189097587963186073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867595170926901235162861 325348189097587963186073)
                    ·
                      refine ⟨244011141823190972389555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325348189097587963186073 244011141823190972389555)
                      ·
                        rfl

theorem cell23_475210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_475210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475210 prefixEnd_475210 := by exact prefixLift 475210
  have htrace : WordTrace (prefixWord ++ tailWord_475210) baseStart_475210 baseEnd_475210 := by
    simpa [prefixWord, tailWord_475210, baseEnd_475210] using wordTrace_append hprefix tailTrace_475210
  have hstable : (prefixWord ++ tailWord_475210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475210).length < 2 ^ (prefixWord ++ tailWord_475210).sum := by decide
  have hdescent : baseEnd_475210 < baseStart_475210 := by decide
  rcases family_descends (prefixWord ++ tailWord_475210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475216 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_475216 : Nat := 118140960795 + 475216 * 2 ^ 59
def prefixEnd_475216 : Nat := 4983230072969 + 3 ^ 40 * 475216 * 2
def baseEnd_475216 : Nat := 81338074235705982971509

theorem tailTrace_475216 : CollatzResearch.WordTrace tailWord_475216 prefixEnd_475216 81338074235705982971509 := by
  unfold tailWord_475216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666275723190533638198751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11555034297587378184265001 8666275723190533638198751)
  ·
    refine ⟨12999413584785800457298127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8666275723190533638198751 12999413584785800457298127)
    ·
      refine ⟨19499120377178700685947191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999413584785800457298127 19499120377178700685947191)
      ·
        refine ⟨29248680565768051028920787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19499120377178700685947191 29248680565768051028920787)
        ·
          refine ⟨43873020848652076543381181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29248680565768051028920787 43873020848652076543381181)
          ·
            refine ⟨16452382818244528703767943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43873020848652076543381181 16452382818244528703767943)
            ·
              refine ⟨24678574227366793055651915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16452382818244528703767943 24678574227366793055651915)
              ·
                refine ⟨37017861341050189583477873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24678574227366793055651915 37017861341050189583477873)
                ·
                  refine ⟨27763396005787642187608405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37017861341050189583477873 27763396005787642187608405)
                  ·
                    refine ⟨81338074235705982971509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 27763396005787642187608405 81338074235705982971509)
                    ·
                      rfl

theorem cell23_475216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_475216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475216 prefixEnd_475216 := by exact prefixLift 475216
  have htrace : WordTrace (prefixWord ++ tailWord_475216) baseStart_475216 baseEnd_475216 := by
    simpa [prefixWord, tailWord_475216, baseEnd_475216] using wordTrace_append hprefix tailTrace_475216
  have hstable : (prefixWord ++ tailWord_475216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475216).length < 2 ^ (prefixWord ++ tailWord_475216).sum := by decide
  have hdescent : baseEnd_475216 < baseStart_475216 := by decide
  rcases family_descends (prefixWord ++ tailWord_475216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475223 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_475223 : Nat := 118140960795 + 475223 * 2 ^ 59
def prefixEnd_475223 : Nat := 4983230072969 + 3 ^ 40 * 475223 * 2
def baseEnd_475223 : Nat := 244017817071699421526995

theorem tailTrace_475223 : CollatzResearch.WordTrace tailWord_475223 prefixEnd_475223 244017817071699421526995 := by
  unfold tailWord_475223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17332806757355707471902323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11555204504903804981268215 17332806757355707471902323)
  ·
    refine ⟨25999210136033561207853485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17332806757355707471902323 25999210136033561207853485)
    ·
      refine ⟨9749703801012585452945057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25999210136033561207853485 9749703801012585452945057)
      ·
        refine ⟨7312277850759439089708793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9749703801012585452945057 7312277850759439089708793)
        ·
          refine ⟨5484208388069579317281595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7312277850759439089708793 5484208388069579317281595)
          ·
            refine ⟨8226312582104368975922393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484208388069579317281595 8226312582104368975922393)
            ·
              refine ⟨6169734436578276731941795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226312582104368975922393 6169734436578276731941795)
              ·
                refine ⟨9254601654867415097912693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169734436578276731941795 9254601654867415097912693)
                ·
                  refine ⟨867618905143820165429315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9254601654867415097912693 867618905143820165429315)
                  ·
                    refine ⟨1301428357715730248143973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 867618905143820165429315 1301428357715730248143973)
                    ·
                      refine ⟨244017817071699421526995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1301428357715730248143973 244017817071699421526995)
                      ·
                        rfl

theorem cell23_475223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_475223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475223 prefixEnd_475223 := by exact prefixLift 475223
  have htrace : WordTrace (prefixWord ++ tailWord_475223) baseStart_475223 baseEnd_475223 := by
    simpa [prefixWord, tailWord_475223, baseEnd_475223] using wordTrace_append hprefix tailTrace_475223
  have hstable : (prefixWord ++ tailWord_475223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475223).length < 2 ^ (prefixWord ++ tailWord_475223).sum := by decide
  have hdescent : baseEnd_475223 < baseStart_475223 := by decide
  rcases family_descends (prefixWord ++ tailWord_475223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475250 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_475250 : Nat := 118140960795 + 475250 * 2 ^ 59
def prefixEnd_475250 : Nat := 4983230072969 + 3 ^ 40 * 475250 * 2
def baseEnd_475250 : Nat := 81343893683123605296457

theorem tailTrace_475250 : CollatzResearch.WordTrace tailWord_475250 prefixEnd_475250 81343893683123605296457 := by
  unfold tailWord_475250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333447882064472770783801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11555861018838594055423469 4333447882064472770783801)
  ·
    refine ⟨3250085911548354578087851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4333447882064472770783801 3250085911548354578087851)
    ·
      refine ⟨4875128867322531867131777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250085911548354578087851 4875128867322531867131777)
      ·
        refine ⟨3656346650491898900348833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4875128867322531867131777 3656346650491898900348833)
        ·
          refine ⟨2742259987868924175261625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656346650491898900348833 2742259987868924175261625)
          ·
            refine ⟨2056694990901693131446219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742259987868924175261625 2056694990901693131446219)
            ·
              refine ⟨3085042486352539697169329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056694990901693131446219 3085042486352539697169329)
              ·
                refine ⟨2313781864764404772876997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085042486352539697169329 2313781864764404772876997)
                ·
                  refine ⟨433834099643325894914437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313781864764404772876997 433834099643325894914437)
                  ·
                    refine ⟨81343893683123605296457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433834099643325894914437 81343893683123605296457)
                    ·
                      rfl

theorem cell23_475250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_475250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475250 prefixEnd_475250 := by exact prefixLift 475250
  have htrace : WordTrace (prefixWord ++ tailWord_475250) baseStart_475250 baseEnd_475250 := by
    simpa [prefixWord, tailWord_475250, baseEnd_475250] using wordTrace_append hprefix tailTrace_475250
  have hstable : (prefixWord ++ tailWord_475250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475250).length < 2 ^ (prefixWord ++ tailWord_475250).sum := by decide
  have hdescent : baseEnd_475250 < baseStart_475250 := by decide
  rcases family_descends (prefixWord ++ tailWord_475250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475260 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_475260 : Nat := 118140960795 + 475260 * 2 ^ 59
def prefixEnd_475260 : Nat := 4983230072969 + 3 ^ 40 * 475260 * 2
def baseEnd_475260 : Nat := 244036815855915776764325

theorem tailTrace_475260 : CollatzResearch.WordTrace tailWord_475260 prefixEnd_475260 244036815855915776764325 := by
  unfold tailWord_475260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667078129110831395499617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11556104172147775193999489 8667078129110831395499617)
  ·
    refine ⟨6500308596833123546624713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8667078129110831395499617 6500308596833123546624713)
    ·
      refine ⟨4875231447624842659968535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500308596833123546624713 4875231447624842659968535)
      ·
        refine ⟨7312847171437263989952803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875231447624842659968535 7312847171437263989952803)
        ·
          refine ⟨10969270757155895984929205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312847171437263989952803 10969270757155895984929205)
          ·
            refine ⟨1028369133483365248587113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10969270757155895984929205 1028369133483365248587113)
            ·
              refine ⟨771276850112523936440335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028369133483365248587113 771276850112523936440335)
              ·
                refine ⟨1156915275168785904660503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771276850112523936440335 1156915275168785904660503)
                ·
                  refine ⟨1735372912753178856990755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156915275168785904660503 1735372912753178856990755)
                  ·
                    refine ⟨2603059369129768285486133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735372912753178856990755 2603059369129768285486133)
                    ·
                      refine ⟨244036815855915776764325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2603059369129768285486133 244036815855915776764325)
                      ·
                        rfl

theorem cell23_475260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_475260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475260 prefixEnd_475260 := by exact prefixLift 475260
  have htrace : WordTrace (prefixWord ++ tailWord_475260) baseStart_475260 baseEnd_475260 := by
    simpa [prefixWord, tailWord_475260, baseEnd_475260] using wordTrace_append hprefix tailTrace_475260
  have hstable : (prefixWord ++ tailWord_475260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475260).length < 2 ^ (prefixWord ++ tailWord_475260).sum := by decide
  have hdescent : baseEnd_475260 < baseStart_475260 := by decide
  rcases family_descends (prefixWord ++ tailWord_475260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475274 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2]
def baseStart_475274 : Nat := 118140960795 + 475274 * 2 ^ 59
def prefixEnd_475274 : Nat := 4983230072969 + 3 ^ 40 * 475274 * 2
def baseEnd_475274 : Nat := 244044004585078721989261

theorem tailTrace_475274 : CollatzResearch.WordTrace tailWord_475274 prefixEnd_475274 244044004585078721989261 := by
  unfold tailWord_475274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333666720042735795502219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11556444586780628788005917 4333666720042735795502219)
  ·
    refine ⟨6500500080064103693253329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333666720042735795502219 6500500080064103693253329)
    ·
      refine ⟨4875375060048077769939997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500500080064103693253329 4875375060048077769939997)
      ·
        refine ⟨1828265647518029163727499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4875375060048077769939997 1828265647518029163727499)
        ·
          refine ⟨2742398471277043745591249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828265647518029163727499 2742398471277043745591249)
          ·
            refine ⟨2056798853457782809193437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742398471277043745591249 2056798853457782809193437)
            ·
              refine ⟨771299570046668553447539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2056798853457782809193437 771299570046668553447539)
              ·
                refine ⟨1156949355070002830171309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771299570046668553447539 1156949355070002830171309)
                ·
                  refine ⟨433856008151251061314241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156949355070002830171309 433856008151251061314241)
                  ·
                    refine ⟨325392006113438295985681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433856008151251061314241 325392006113438295985681)
                    ·
                      refine ⟨244044004585078721989261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325392006113438295985681 244044004585078721989261)
                      ·
                        rfl

theorem cell23_475274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_475274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475274 prefixEnd_475274 := by exact prefixLift 475274
  have htrace : WordTrace (prefixWord ++ tailWord_475274) baseStart_475274 baseEnd_475274 := by
    simpa [prefixWord, tailWord_475274, baseEnd_475274] using wordTrace_append hprefix tailTrace_475274
  have hstable : (prefixWord ++ tailWord_475274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475274).length < 2 ^ (prefixWord ++ tailWord_475274).sum := by decide
  have hdescent : baseEnd_475274 < baseStart_475274 := by decide
  rcases family_descends (prefixWord ++ tailWord_475274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475294 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_475294 : Nat := 118140960795 + 475294 * 2 ^ 59
def prefixEnd_475294 : Nat := 4983230072969 + 3 ^ 40 * 475294 * 2
def baseEnd_475294 : Nat := 244054274198168643739169

theorem tailTrace_475294 : CollatzResearch.WordTrace tailWord_475294 prefixEnd_475294 244054274198168643739169 := by
  unfold tailWord_475294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166924542512310824717117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11556930893398991065157957 2166924542512310824717117)
  ·
    refine ⟨812596703442116559268919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2166924542512310824717117 812596703442116559268919)
    ·
      refine ⟨1218895055163174838903379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812596703442116559268919 1218895055163174838903379)
      ·
        refine ⟨1828342582744762258355069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218895055163174838903379 1828342582744762258355069)
        ·
          refine ⟨685628468529285846883151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1828342582744762258355069 685628468529285846883151)
          ·
            refine ⟨1028442702793928770324727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685628468529285846883151 1028442702793928770324727)
            ·
              refine ⟨1542664054190893155487091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028442702793928770324727 1542664054190893155487091)
              ·
                refine ⟨2313996081286339733230637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542664054190893155487091 2313996081286339733230637)
                ·
                  refine ⟨867748530482377399961489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2313996081286339733230637 867748530482377399961489)
                  ·
                    refine ⟨650811397861783049971117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867748530482377399961489 650811397861783049971117)
                    ·
                      refine ⟨244054274198168643739169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650811397861783049971117 244054274198168643739169)
                      ·
                        rfl

theorem cell23_475294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_475294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475294 prefixEnd_475294 := by exact prefixLift 475294
  have htrace : WordTrace (prefixWord ++ tailWord_475294) baseStart_475294 baseEnd_475294 := by
    simpa [prefixWord, tailWord_475294, baseEnd_475294] using wordTrace_append hprefix tailTrace_475294
  have hstable : (prefixWord ++ tailWord_475294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475294).length < 2 ^ (prefixWord ++ tailWord_475294).sum := by decide
  have hdescent : baseEnd_475294 < baseStart_475294 := by decide
  rcases family_descends (prefixWord ++ tailWord_475294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475323 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 2, 6]
def baseStart_475323 : Nat := 118140960795 + 475323 * 2 ^ 59
def prefixEnd_475323 : Nat := 4983230072969 + 3 ^ 40 * 475323 * 2
def baseEnd_475323 : Nat := 81356388379049676758845

theorem tailTrace_475323 : CollatzResearch.WordTrace tailWord_475323 prefixEnd_475323 81356388379049676758845 := by
  unfold tailWord_475323
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336454056993424550542623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11557636037995616367028415 17336454056993424550542623)
  ·
    refine ⟨26004681085490136825813935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17336454056993424550542623 26004681085490136825813935)
    ·
      refine ⟨39007021628235205238720903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26004681085490136825813935 39007021628235205238720903)
      ·
        refine ⟨58510532442352807858081355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39007021628235205238720903 58510532442352807858081355)
        ·
          refine ⟨87765798663529211787122033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58510532442352807858081355 87765798663529211787122033)
          ·
            refine ⟨65824348997646908840341525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87765798663529211787122033 65824348997646908840341525)
            ·
              refine ⟨3085516359264698851891009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65824348997646908840341525 3085516359264698851891009)
              ·
                refine ⟨2314137269448524138918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085516359264698851891009 2314137269448524138918257)
                ·
                  refine ⟨1735602952086393104188693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314137269448524138918257 1735602952086393104188693)
                  ·
                    refine ⟨81356388379049676758845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1735602952086393104188693 81356388379049676758845)
                    ·
                      rfl

theorem cell23_475323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_475323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475323 prefixEnd_475323 := by exact prefixLift 475323
  have htrace : WordTrace (prefixWord ++ tailWord_475323) baseStart_475323 baseEnd_475323 := by
    simpa [prefixWord, tailWord_475323, baseEnd_475323] using wordTrace_append hprefix tailTrace_475323
  have hstable : (prefixWord ++ tailWord_475323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475323).length < 2 ^ (prefixWord ++ tailWord_475323).sum := by decide
  have hdescent : baseEnd_475323 < baseStart_475323 := by decide
  rcases family_descends (prefixWord ++ tailWord_475323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475333 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_475333 : Nat := 118140960795 + 475333 * 2 ^ 59
def prefixEnd_475333 : Nat := 4983230072969 + 3 ^ 40 * 475333 * 2
def baseEnd_475333 : Nat := 244074299943693991151489

theorem tailTrace_475333 : CollatzResearch.WordTrace tailWord_475333 prefixEnd_475333 244074299943693991151489 := by
  unfold tailWord_475333
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336818786957196258406653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11557879191304797505604435 17336818786957196258406653)
  ·
    refine ⟨6501307045108948596902495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17336818786957196258406653 6501307045108948596902495)
    ·
      refine ⟨9751960567663422895353743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501307045108948596902495 9751960567663422895353743)
      ·
        refine ⟨14627940851495134343030615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751960567663422895353743 14627940851495134343030615)
        ·
          refine ⟨21941911277242701514545923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627940851495134343030615 21941911277242701514545923)
          ·
            refine ⟨32912866915864052271818885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21941911277242701514545923 32912866915864052271818885)
            ·
              refine ⟨6171162546724509800966041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32912866915864052271818885 6171162546724509800966041)
              ·
                refine ⟨4628371910043382350724531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171162546724509800966041 4628371910043382350724531)
                ·
                  refine ⟨6942557865065073526086797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628371910043382350724531 6942557865065073526086797)
                  ·
                    refine ⟨2603459199399402572282549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6942557865065073526086797 2603459199399402572282549)
                    ·
                      refine ⟨244074299943693991151489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2603459199399402572282549 244074299943693991151489)
                      ·
                        rfl

theorem cell23_475333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_475333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475333 prefixEnd_475333 := by exact prefixLift 475333
  have htrace : WordTrace (prefixWord ++ tailWord_475333) baseStart_475333 baseEnd_475333 := by
    simpa [prefixWord, tailWord_475333, baseEnd_475333] using wordTrace_append hprefix tailTrace_475333
  have hstable : (prefixWord ++ tailWord_475333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475333).length < 2 ^ (prefixWord ++ tailWord_475333).sum := by decide
  have hdescent : baseEnd_475333 < baseStart_475333 := by decide
  rcases family_descends (prefixWord ++ tailWord_475333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475353 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 9]
def baseStart_475353 : Nat := 118140960795 + 475353 * 2 ^ 59
def prefixEnd_475353 : Nat := 4983230072969 + 3 ^ 40 * 475353 * 2
def baseEnd_475353 : Nat := 27120507728531545877933

theorem tailTrace_475353 : CollatzResearch.WordTrace tailWord_475353 prefixEnd_475353 27120507728531545877933 := by
  unfold tailWord_475353
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337548246884739674134713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11558365497923159782756475 17337548246884739674134713)
  ·
    refine ⟨13003161185163554755601035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17337548246884739674134713 13003161185163554755601035)
    ·
      refine ⟨19504741777745332133401553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13003161185163554755601035 19504741777745332133401553)
      ·
        refine ⟨14628556333308999100051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19504741777745332133401553 14628556333308999100051165)
        ·
          refine ⟨5485708624990874662519187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14628556333308999100051165 5485708624990874662519187)
          ·
            refine ⟨8228562937486311993778781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485708624990874662519187 8228562937486311993778781)
            ·
              refine ⟨3085711101557366997667043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8228562937486311993778781 3085711101557366997667043)
              ·
                refine ⟨4628566652336050496500565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085711101557366997667043 4628566652336050496500565)
                ·
                  refine ⟨27120507728531545877933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4628566652336050496500565 27120507728531545877933)
                  ·
                    rfl

theorem cell23_475353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_475353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475353 prefixEnd_475353 := by exact prefixLift 475353
  have htrace : WordTrace (prefixWord ++ tailWord_475353) baseStart_475353 baseEnd_475353 := by
    simpa [prefixWord, tailWord_475353, baseEnd_475353] using wordTrace_append hprefix tailTrace_475353
  have hstable : (prefixWord ++ tailWord_475353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475353).length < 2 ^ (prefixWord ++ tailWord_475353).sum := by decide
  have hdescent : baseEnd_475353 < baseStart_475353 := by decide
  rcases family_descends (prefixWord ++ tailWord_475353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475362 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_475362 : Nat := 118140960795 + 475362 * 2 ^ 59
def prefixEnd_475362 : Nat := 4983230072969 + 3 ^ 40 * 475362 * 2
def baseEnd_475362 : Nat := 244089190882674377688857

theorem tailTrace_475362 : CollatzResearch.WordTrace tailWord_475362 prefixEnd_475362 244089190882674377688857 := by
  unfold tailWord_475362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334469125963033552803085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11558584335901422807474893 4334469125963033552803085)
  ·
    refine ⟨1625425922236137582301157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4334469125963033552803085 1625425922236137582301157)
    ·
      refine ⟨304767360419275796681467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1625425922236137582301157 304767360419275796681467)
      ·
        refine ⟨457151040628913695022201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304767360419275796681467 457151040628913695022201)
        ·
          refine ⟨342863280471685271266651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457151040628913695022201 342863280471685271266651)
          ·
            refine ⟨514294920707527906899977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342863280471685271266651 514294920707527906899977)
            ·
              refine ⟨385721190530645930174983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514294920707527906899977 385721190530645930174983)
              ·
                refine ⟨578581785795968895262475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385721190530645930174983 578581785795968895262475)
                ·
                  refine ⟨867872678693953342893713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578581785795968895262475 867872678693953342893713)
                  ·
                    refine ⟨650904509020465007170285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 867872678693953342893713 650904509020465007170285)
                    ·
                      refine ⟨244089190882674377688857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 650904509020465007170285 244089190882674377688857)
                      ·
                        rfl

theorem cell23_475362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_475362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475362 prefixEnd_475362 := by exact prefixLift 475362
  have htrace : WordTrace (prefixWord ++ tailWord_475362) baseStart_475362 baseEnd_475362 := by
    simpa [prefixWord, tailWord_475362, baseEnd_475362] using wordTrace_append hprefix tailTrace_475362
  have hstable : (prefixWord ++ tailWord_475362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475362).length < 2 ^ (prefixWord ++ tailWord_475362).sum := by decide
  have hdescent : baseEnd_475362 < baseStart_475362 := by decide
  rcases family_descends (prefixWord ++ tailWord_475362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475383 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 7]
def baseStart_475383 : Nat := 118140960795 + 475383 * 2 ^ 59
def prefixEnd_475383 : Nat := 4983230072969 + 3 ^ 40 * 475383 * 2
def baseEnd_475383 : Nat := 81366657992139598508753

theorem tailTrace_475383 : CollatzResearch.WordTrace tailWord_475383 prefixEnd_475383 81366657992139598508753 := by
  unfold tailWord_475383
  simp only [CollatzResearch.WordTrace]
  refine ⟨17338642436776054797726803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11559094957850703198484535 17338642436776054797726803)
  ·
    refine ⟨26007963655164082196590205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17338642436776054797726803 26007963655164082196590205)
    ·
      refine ⟨9752986370686530823721327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26007963655164082196590205 9752986370686530823721327)
      ·
        refine ⟨14629479556029796235581991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9752986370686530823721327 14629479556029796235581991)
        ·
          refine ⟨21944219334044694353372987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14629479556029796235581991 21944219334044694353372987)
          ·
            refine ⟨32916329001067041530059481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21944219334044694353372987 32916329001067041530059481)
            ·
              refine ⟨24687246750800281147544611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32916329001067041530059481 24687246750800281147544611)
              ·
                refine ⟨37030870126200421721316917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24687246750800281147544611 37030870126200421721316917)
                ·
                  refine ⟨3471644074331289536373461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37030870126200421721316917 3471644074331289536373461)
                  ·
                    refine ⟨81366657992139598508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3471644074331289536373461 81366657992139598508753)
                    ·
                      rfl

theorem cell23_475383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_475383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475383 prefixEnd_475383 := by exact prefixLift 475383
  have htrace : WordTrace (prefixWord ++ tailWord_475383) baseStart_475383 baseEnd_475383 := by
    simpa [prefixWord, tailWord_475383, baseEnd_475383] using wordTrace_append hprefix tailTrace_475383
  have hstable : (prefixWord ++ tailWord_475383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475383).length < 2 ^ (prefixWord ++ tailWord_475383).sum := by decide
  have hdescent : baseEnd_475383 < baseStart_475383 := by decide
  rcases family_descends (prefixWord ++ tailWord_475383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475400 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_475400 : Nat := 118140960795 + 475400 * 2 ^ 59
def prefixEnd_475400 : Nat := 4983230072969 + 3 ^ 40 * 475400 * 2
def baseEnd_475400 : Nat := 81369567715848409671227

theorem tailTrace_475400 : CollatzResearch.WordTrace tailWord_475400 prefixEnd_475400 81369567715848409671227 := by
  unfold tailWord_475400
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669631238857233350547827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11559508318476311134063769 8669631238857233350547827)
  ·
    refine ⟨13004446858285850025821741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669631238857233350547827 13004446858285850025821741)
    ·
      refine ⟨4876667571857193759683153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13004446858285850025821741 4876667571857193759683153)
      ·
        refine ⟨3657500678892895319762365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876667571857193759683153 3657500678892895319762365)
        ·
          refine ⟨1371562754584835744910887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3657500678892895319762365 1371562754584835744910887)
          ·
            refine ⟨2057344131877253617366331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371562754584835744910887 2057344131877253617366331)
            ·
              refine ⟨3086016197815880426049497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057344131877253617366331 3086016197815880426049497)
              ·
                refine ⟨2314512148361910319537123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086016197815880426049497 2314512148361910319537123)
                ·
                  refine ⟨3471768222542865479305685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314512148361910319537123 3471768222542865479305685)
                  ·
                    refine ⟨81369567715848409671227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3471768222542865479305685 81369567715848409671227)
                    ·
                      rfl

theorem cell23_475400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_475400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475400 prefixEnd_475400 := by exact prefixLift 475400
  have htrace : WordTrace (prefixWord ++ tailWord_475400) baseStart_475400 baseEnd_475400 := by
    simpa [prefixWord, tailWord_475400, baseEnd_475400] using wordTrace_append hprefix tailTrace_475400
  have hstable : (prefixWord ++ tailWord_475400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475400).length < 2 ^ (prefixWord ++ tailWord_475400).sum := by decide
  have hdescent : baseEnd_475400 < baseStart_475400 := by decide
  rcases family_descends (prefixWord ++ tailWord_475400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475421 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 5]
def baseStart_475421 : Nat := 118140960795 + 475421 * 2 ^ 59
def prefixEnd_475421 : Nat := 4983230072969 + 3 ^ 40 * 475421 * 2
def baseEnd_475421 : Nat := 27124387360143294094565

theorem tailTrace_475421 : CollatzResearch.WordTrace tailWord_475421 prefixEnd_475421 27124387360143294094565 := by
  unfold tailWord_475421
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340028410638387287610117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11560018940425591525073411 17340028410638387287610117)
  ·
    refine ⟨3251255326994697616426897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17340028410638387287610117 3251255326994697616426897)
    ·
      refine ⟨2438441495246023212320173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3251255326994697616426897 2438441495246023212320173)
      ·
        refine ⟨914415560717258704620065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2438441495246023212320173 914415560717258704620065)
        ·
          refine ⟨685811670537944028465049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914415560717258704620065 685811670537944028465049)
          ·
            refine ⟨514358752903458021348787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685811670537944028465049 514358752903458021348787)
            ·
              refine ⟨771538129355187032023181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514358752903458021348787 771538129355187032023181)
              ·
                refine ⟨289326798508195137008693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771538129355187032023181 289326798508195137008693)
                ·
                  refine ⟨27124387360143294094565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289326798508195137008693 27124387360143294094565)
                  ·
                    rfl

theorem cell23_475421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_475421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475421 prefixEnd_475421 := by exact prefixLift 475421
  have htrace : WordTrace (prefixWord ++ tailWord_475421) baseStart_475421 baseEnd_475421 := by
    simpa [prefixWord, tailWord_475421, baseEnd_475421] using wordTrace_append hprefix tailTrace_475421
  have hstable : (prefixWord ++ tailWord_475421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475421).length < 2 ^ (prefixWord ++ tailWord_475421).sum := by decide
  have hdescent : baseEnd_475421 < baseStart_475421 := by decide
  rcases family_descends (prefixWord ++ tailWord_475421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475434 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_475434 : Nat := 118140960795 + 475434 * 2 ^ 59
def prefixEnd_475434 : Nat := 4983230072969 + 3 ^ 40 * 475434 * 2
def baseEnd_475434 : Nat := 81375387163266031996175

theorem tailTrace_475434 : CollatzResearch.WordTrace tailWord_475434 prefixEnd_475434 81375387163266031996175 := by
  unfold tailWord_475434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335125639897822626958339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11560335039727527005222237 4335125639897822626958339)
  ·
    refine ⟨6502688459846733940437509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335125639897822626958339 6502688459846733940437509)
    ·
      refine ⟨1219254086221262613832033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6502688459846733940437509 1219254086221262613832033)
      ·
        refine ⟨914440564665946960374025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219254086221262613832033 914440564665946960374025)
        ·
          refine ⟨685830423499460220280519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914440564665946960374025 685830423499460220280519)
          ·
            refine ⟨1028745635249190330420779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685830423499460220280519 1028745635249190330420779)
            ·
              refine ⟨1543118452873785495631169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028745635249190330420779 1543118452873785495631169)
              ·
                refine ⟨1157338839655339121723377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543118452873785495631169 1157338839655339121723377)
                ·
                  refine ⟨868004129741504341292533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157338839655339121723377 868004129741504341292533)
                  ·
                    refine ⟨81375387163266031996175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 868004129741504341292533 81375387163266031996175)
                    ·
                      rfl

theorem cell23_475434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_475434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475434 prefixEnd_475434 := by exact prefixLift 475434
  have htrace : WordTrace (prefixWord ++ tailWord_475434) baseStart_475434 baseEnd_475434 := by
    simpa [prefixWord, tailWord_475434, baseEnd_475434] using wordTrace_append hprefix tailTrace_475434
  have hstable : (prefixWord ++ tailWord_475434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475434).length < 2 ^ (prefixWord ++ tailWord_475434).sum := by decide
  have hdescent : baseEnd_475434 < baseStart_475434 := by decide
  rcases family_descends (prefixWord ++ tailWord_475434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475438 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_475438 : Nat := 118140960795 + 475438 * 2 ^ 59
def prefixEnd_475438 : Nat := 4983230072969 + 3 ^ 40 * 475438 * 2
def baseEnd_475438 : Nat := 27125357268046231148723

theorem tailTrace_475438 : CollatzResearch.WordTrace tailWord_475438 prefixEnd_475438 27125357268046231148723 := by
  unfold tailWord_475438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167581056447099898872371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11560432301051199460652645 2167581056447099898872371)
  ·
    refine ⟨3251371584670649848308557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2167581056447099898872371 3251371584670649848308557)
    ·
      refine ⟨1219264344251493693115709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3251371584670649848308557 1219264344251493693115709)
      ·
        refine ⟨457224129094310134918391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1219264344251493693115709 457224129094310134918391)
        ·
          refine ⟨685836193641465202377587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457224129094310134918391 685836193641465202377587)
          ·
            refine ⟨1028754290462197803566381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685836193641465202377587 1028754290462197803566381)
            ·
              refine ⟨385782858923324176337393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1028754290462197803566381 385782858923324176337393)
              ·
                refine ⟨289337144192493132253045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385782858923324176337393 289337144192493132253045)
                ·
                  refine ⟨27125357268046231148723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289337144192493132253045 27125357268046231148723)
                  ·
                    rfl

theorem cell23_475438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_475438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475438 prefixEnd_475438 := by exact prefixLift 475438
  have htrace : WordTrace (prefixWord ++ tailWord_475438) baseStart_475438 baseEnd_475438 := by
    simpa [prefixWord, tailWord_475438, baseEnd_475438] using wordTrace_append hprefix tailTrace_475438
  have hstable : (prefixWord ++ tailWord_475438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475438).length < 2 ^ (prefixWord ++ tailWord_475438).sum := by decide
  have hdescent : baseEnd_475438 < baseStart_475438 := by decide
  rcases family_descends (prefixWord ++ tailWord_475438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475440 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_475440 : Nat := 118140960795 + 475440 * 2 ^ 59
def prefixEnd_475440 : Nat := 4983230072969 + 3 ^ 40 * 475440 * 2
def baseEnd_475440 : Nat := 244129242373725072513497

theorem tailTrace_475440 : CollatzResearch.WordTrace tailWord_475440 prefixEnd_475440 244129242373725072513497 := by
  unfold tailWord_475440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670360698784776766275887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11560480931713035688367849 8670360698784776766275887)
  ·
    refine ⟨13005541048177165149413831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8670360698784776766275887 13005541048177165149413831)
    ·
      refine ⟨19508311572265747724120747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005541048177165149413831 19508311572265747724120747)
      ·
        refine ⟨29262467358398621586181121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508311572265747724120747 29262467358398621586181121)
        ·
          refine ⟨21946850518798966189635841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29262467358398621586181121 21946850518798966189635841)
          ·
            refine ⟨16460137889099224642226881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21946850518798966189635841 16460137889099224642226881)
            ·
              refine ⟨12345103416824418481670161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16460137889099224642226881 12345103416824418481670161)
              ·
                refine ⟨9258827562618313861252621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12345103416824418481670161 9258827562618313861252621)
                ·
                  refine ⟨3472060335981867697969733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9258827562618313861252621 3472060335981867697969733)
                  ·
                    refine ⟨651011312996600193369325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3472060335981867697969733 651011312996600193369325)
                    ·
                      refine ⟨244129242373725072513497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651011312996600193369325 244129242373725072513497)
                      ·
                        rfl

theorem cell23_475440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_475440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475440 prefixEnd_475440 := by exact prefixLift 475440
  have htrace : WordTrace (prefixWord ++ tailWord_475440) baseStart_475440 baseEnd_475440 := by
    simpa [prefixWord, tailWord_475440, baseEnd_475440] using wordTrace_append hprefix tailTrace_475440
  have hstable : (prefixWord ++ tailWord_475440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475440).length < 2 ^ (prefixWord ++ tailWord_475440).sum := by decide
  have hdescent : baseEnd_475440 < baseStart_475440 := by decide
  rcases family_descends (prefixWord ++ tailWord_475440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475498 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_475498 : Nat := 118140960795 + 475498 * 2 ^ 59
def prefixEnd_475498 : Nat := 4983230072969 + 3 ^ 40 * 475498 * 2
def baseEnd_475498 : Nat := 81386341417228615196077

theorem tailTrace_475498 : CollatzResearch.WordTrace tailWord_475498 prefixEnd_475498 81386341417228615196077 := by
  unfold tailWord_475498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4335709207839857359540787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11561891220906286292108765 4335709207839857359540787)
  ·
    refine ⟨6503563811759786039311181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4335709207839857359540787 6503563811759786039311181)
    ·
      refine ⟨2438836429409919764741693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6503563811759786039311181 2438836429409919764741693)
      ·
        refine ⟨914563661028719911778135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2438836429409919764741693 914563661028719911778135)
        ·
          refine ⟨1371845491543079867667203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914563661028719911778135 1371845491543079867667203)
          ·
            refine ⟨2057768237314619801500805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371845491543079867667203 2057768237314619801500805)
            ·
              refine ⟨385831544496491212781401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2057768237314619801500805 385831544496491212781401)
              ·
                refine ⟨289373658372368409586051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385831544496491212781401 289373658372368409586051)
                ·
                  refine ⟨434060487558552614379077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289373658372368409586051 434060487558552614379077)
                  ·
                    refine ⟨81386341417228615196077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434060487558552614379077 81386341417228615196077)
                    ·
                      rfl

theorem cell23_475498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_475498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475498 prefixEnd_475498 := by exact prefixLift 475498
  have htrace : WordTrace (prefixWord ++ tailWord_475498) baseStart_475498 baseEnd_475498 := by
    simpa [prefixWord, tailWord_475498, baseEnd_475498] using wordTrace_append hprefix tailTrace_475498
  have hstable : (prefixWord ++ tailWord_475498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475498).length < 2 ^ (prefixWord ++ tailWord_475498).sum := by decide
  have hdescent : baseEnd_475498 < baseStart_475498 := by decide
  rcases family_descends (prefixWord ++ tailWord_475498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475521 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_475521 : Nat := 118140960795 + 475521 * 2 ^ 59
def prefixEnd_475521 : Nat := 4983230072969 + 3 ^ 40 * 475521 * 2
def baseEnd_475521 : Nat := 244170834306739255600625

theorem tailTrace_475521 : CollatzResearch.WordTrace tailWord_475521 prefixEnd_475521 244170834306739255600625 := by
  unfold tailWord_475521
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343675710276104366250417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11562450473517402910833611 17343675710276104366250417)
  ·
    refine ⟨13007756782707078274687813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17343675710276104366250417 13007756782707078274687813)
    ·
      refine ⟨2438954396757577176503965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13007756782707078274687813 2438954396757577176503965)
      ·
        refine ⟨914607898784091441188987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2438954396757577176503965 914607898784091441188987)
        ·
          refine ⟨1371911848176137161783481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914607898784091441188987 1371911848176137161783481)
          ·
            refine ⟨1028933886132102871337611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371911848176137161783481 1028933886132102871337611)
            ·
              refine ⟨1543400829198154307006417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028933886132102871337611 1543400829198154307006417)
              ·
                refine ⟨1157550621898615730254813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543400829198154307006417 1157550621898615730254813)
                ·
                  refine ⟨434081483211980898845555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157550621898615730254813 434081483211980898845555)
                  ·
                    refine ⟨651122224817971348268333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434081483211980898845555 651122224817971348268333)
                    ·
                      refine ⟨244170834306739255600625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651122224817971348268333 244170834306739255600625)
                      ·
                        rfl

theorem cell23_475521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_475521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475521 prefixEnd_475521 := by exact prefixLift 475521
  have htrace : WordTrace (prefixWord ++ tailWord_475521) baseStart_475521 baseEnd_475521 := by
    simpa [prefixWord, tailWord_475521, baseEnd_475521] using wordTrace_append hprefix tailTrace_475521
  have hstable : (prefixWord ++ tailWord_475521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475521).length < 2 ^ (prefixWord ++ tailWord_475521).sum := by decide
  have hdescent : baseEnd_475521 < baseStart_475521 := by decide
  rcases family_descends (prefixWord ++ tailWord_475521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475527 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_475527 : Nat := 118140960795 + 475527 * 2 ^ 59
def prefixEnd_475527 : Nat := 4983230072969 + 3 ^ 40 * 475527 * 2
def baseEnd_475527 : Nat := 244173915190666232125597

theorem tailTrace_475527 : CollatzResearch.WordTrace tailWord_475527 prefixEnd_475527 244173915190666232125597 := by
  unfold tailWord_475527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343894548254367390968835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11562596365502911593979223 17343894548254367390968835)
  ·
    refine ⟨26015841822381551086453253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17343894548254367390968835 26015841822381551086453253)
    ·
      refine ⟨4877970341696540828709985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26015841822381551086453253 4877970341696540828709985)
      ·
        refine ⟨3658477756272405621532489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4877970341696540828709985 3658477756272405621532489)
        ·
          refine ⟨2743858317204304216149367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658477756272405621532489 2743858317204304216149367)
          ·
            refine ⟨4115787475806456324224051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743858317204304216149367 4115787475806456324224051)
            ·
              refine ⟨6173681213709684486336077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115787475806456324224051 6173681213709684486336077)
              ·
                refine ⟨2315130455141131682376029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173681213709684486336077 2315130455141131682376029)
                ·
                  refine ⟨868173920677924380891011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2315130455141131682376029 868173920677924380891011)
                  ·
                    refine ⟨1302260881016886571336517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868173920677924380891011 1302260881016886571336517)
                    ·
                      refine ⟨244173915190666232125597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1302260881016886571336517 244173915190666232125597)
                      ·
                        rfl

theorem cell23_475527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_475527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475527 prefixEnd_475527 := by exact prefixLift 475527
  have htrace : WordTrace (prefixWord ++ tailWord_475527) baseStart_475527 baseEnd_475527 := by
    simpa [prefixWord, tailWord_475527, baseEnd_475527] using wordTrace_append hprefix tailTrace_475527
  have hstable : (prefixWord ++ tailWord_475527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475527).length < 2 ^ (prefixWord ++ tailWord_475527).sum := by decide
  have hdescent : baseEnd_475527 < baseStart_475527 := by decide
  rcases family_descends (prefixWord ++ tailWord_475527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475531 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 2, 3, 2]
def baseStart_475531 : Nat := 118140960795 + 475531 * 2 ^ 59
def prefixEnd_475531 : Nat := 4983230072969 + 3 ^ 40 * 475531 * 2
def baseEnd_475531 : Nat := 244175969113284216475579

theorem tailTrace_475531 : CollatzResearch.WordTrace tailWord_475531 prefixEnd_475531 244175969113284216475579 := by
  unfold tailWord_475531
  simp only [CollatzResearch.WordTrace]
  refine ⟨17344040440239876074114447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11562693626826584049409631 17344040440239876074114447)
  ·
    refine ⟨26016060660359814111171671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17344040440239876074114447 26016060660359814111171671)
    ·
      refine ⟨39024090990539721166757507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26016060660359814111171671 39024090990539721166757507)
      ·
        refine ⟨58536136485809581750136261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39024090990539721166757507 58536136485809581750136261)
        ·
          refine ⟨10975525591089296578150549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58536136485809581750136261 10975525591089296578150549)
          ·
            refine ⟨514477762082310777100807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10975525591089296578150549 514477762082310777100807)
            ·
              refine ⟨771716643123466165651211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514477762082310777100807 771716643123466165651211)
              ·
                refine ⟨1157574964685199248476817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771716643123466165651211 1157574964685199248476817)
                ·
                  refine ⟨868181223513899436357613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157574964685199248476817 868181223513899436357613)
                  ·
                    refine ⟨325567958817712288634105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868181223513899436357613 325567958817712288634105)
                    ·
                      refine ⟨244175969113284216475579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325567958817712288634105 244175969113284216475579)
                      ·
                        rfl

theorem cell23_475531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3, 2].length) (baseStart_475531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475531 prefixEnd_475531 := by exact prefixLift 475531
  have htrace : WordTrace (prefixWord ++ tailWord_475531) baseStart_475531 baseEnd_475531 := by
    simpa [prefixWord, tailWord_475531, baseEnd_475531] using wordTrace_append hprefix tailTrace_475531
  have hstable : (prefixWord ++ tailWord_475531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475531).length < 2 ^ (prefixWord ++ tailWord_475531).sum := by decide
  have hdescent : baseEnd_475531 < baseStart_475531 := by decide
  rcases family_descends (prefixWord ++ tailWord_475531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475554 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_475554 : Nat := 118140960795 + 475554 * 2 ^ 59
def prefixEnd_475554 : Nat := 4983230072969 + 3 ^ 40 * 475554 * 2
def baseEnd_475554 : Nat := 81395926389445875495991

theorem tailTrace_475554 : CollatzResearch.WordTrace tailWord_475554 prefixEnd_475554 81395926389445875495991 := by
  unfold tailWord_475554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336219829789137750550429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11563252879437700668134477 4336219829789137750550429)
  ·
    refine ⟨1626082436170926656456411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4336219829789137750550429 1626082436170926656456411)
    ·
      refine ⟨2439123654256389984684617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626082436170926656456411 2439123654256389984684617)
      ·
        refine ⟨1829342740692292488513463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439123654256389984684617 1829342740692292488513463)
        ·
          refine ⟨2744014111038438732770195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829342740692292488513463 2744014111038438732770195)
          ·
            refine ⟨4116021166557658099155293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744014111038438732770195 4116021166557658099155293)
            ·
              refine ⟨1543507937459121787183235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4116021166557658099155293 1543507937459121787183235)
              ·
                refine ⟨2315261906188682680774853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543507937459121787183235 2315261906188682680774853)
                ·
                  refine ⟨434111607410378002645285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2315261906188682680774853 434111607410378002645285)
                  ·
                    refine ⟨81395926389445875495991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434111607410378002645285 81395926389445875495991)
                    ·
                      rfl

theorem cell23_475554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_475554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475554 prefixEnd_475554 := by exact prefixLift 475554
  have htrace : WordTrace (prefixWord ++ tailWord_475554) baseStart_475554 baseEnd_475554 := by
    simpa [prefixWord, tailWord_475554, baseEnd_475554] using wordTrace_append hprefix tailTrace_475554
  have hstable : (prefixWord ++ tailWord_475554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475554).length < 2 ^ (prefixWord ++ tailWord_475554).sum := by decide
  have hdescent : baseEnd_475554 < baseStart_475554 := by decide
  rcases family_descends (prefixWord ++ tailWord_475554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475581 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_475581 : Nat := 118140960795 + 475581 * 2 ^ 59
def prefixEnd_475581 : Nat := 4983230072969 + 3 ^ 40 * 475581 * 2
def baseEnd_475581 : Nat := 244201643146009020850349

theorem tailTrace_475581 : CollatzResearch.WordTrace tailWord_475581 prefixEnd_475581 244201643146009020850349 := by
  unfold tailWord_475581
  simp only [CollatzResearch.WordTrace]
  refine ⟨17345864090058734613434597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11563909393372489742289731 17345864090058734613434597)
  ·
    refine ⟨3252349516886012740018987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17345864090058734613434597 3252349516886012740018987)
    ·
      refine ⟨4878524275329019110028481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252349516886012740018987 4878524275329019110028481)
      ·
        refine ⟨3658893206496764332521361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878524275329019110028481 3658893206496764332521361)
        ·
          refine ⟨2744169904872573249391021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658893206496764332521361 2744169904872573249391021)
          ·
            refine ⟨1029063714327214968521633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2744169904872573249391021 1029063714327214968521633)
            ·
              refine ⟨771797785745411226391225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029063714327214968521633 771797785745411226391225)
              ·
                refine ⟨578848339309058419793419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771797785745411226391225 578848339309058419793419)
                ·
                  refine ⟨868272508963587629690129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578848339309058419793419 868272508963587629690129)
                  ·
                    refine ⟨651204381722690722267597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 868272508963587629690129 651204381722690722267597)
                    ·
                      refine ⟨244201643146009020850349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651204381722690722267597 244201643146009020850349)
                      ·
                        rfl

theorem cell23_475581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_475581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475581 prefixEnd_475581 := by exact prefixLift 475581
  have htrace : WordTrace (prefixWord ++ tailWord_475581) baseStart_475581 baseEnd_475581 := by
    simpa [prefixWord, tailWord_475581, baseEnd_475581] using wordTrace_append hprefix tailTrace_475581
  have hstable : (prefixWord ++ tailWord_475581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475581).length < 2 ^ (prefixWord ++ tailWord_475581).sum := by decide
  have hdescent : baseEnd_475581 < baseStart_475581 := by decide
  rcases family_descends (prefixWord ++ tailWord_475581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475594 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_475594 : Nat := 118140960795 + 475594 * 2 ^ 59
def prefixEnd_475594 : Nat := 4983230072969 + 3 ^ 40 * 475594 * 2
def baseEnd_475594 : Nat := 244208318394517469987789

theorem tailTrace_475594 : CollatzResearch.WordTrace tailWord_475594 prefixEnd_475594 244208318394517469987789 := by
  unfold tailWord_475594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336584559752909458414459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11564225492674425222438557 4336584559752909458414459)
  ·
    refine ⟨6504876839629364187621689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4336584559752909458414459 6504876839629364187621689)
    ·
      refine ⟨4878657629722023140716267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6504876839629364187621689 4878657629722023140716267)
      ·
        refine ⟨7317986444583034711074401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878657629722023140716267 7317986444583034711074401)
        ·
          refine ⟨5488489833437276033305801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317986444583034711074401 5488489833437276033305801)
          ·
            refine ⟨4116367375077957024979351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488489833437276033305801 4116367375077957024979351)
            ·
              refine ⟨6174551062616935537469027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116367375077957024979351 6174551062616935537469027)
              ·
                refine ⟨9261826593925403306203541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174551062616935537469027 9261826593925403306203541)
                ·
                  refine ⟨434148121590253279978291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9261826593925403306203541 434148121590253279978291)
                  ·
                    refine ⟨651222182385379919967437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434148121590253279978291 651222182385379919967437)
                    ·
                      refine ⟨244208318394517469987789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651222182385379919967437 244208318394517469987789)
                      ·
                        rfl

theorem cell23_475594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_475594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475594 prefixEnd_475594 := by exact prefixLift 475594
  have htrace : WordTrace (prefixWord ++ tailWord_475594) baseStart_475594 baseEnd_475594 := by
    simpa [prefixWord, tailWord_475594, baseEnd_475594] using wordTrace_append hprefix tailTrace_475594
  have hstable : (prefixWord ++ tailWord_475594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475594).length < 2 ^ (prefixWord ++ tailWord_475594).sum := by decide
  have hdescent : baseEnd_475594 < baseStart_475594 := by decide
  rcases family_descends (prefixWord ++ tailWord_475594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475617 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_475617 : Nat := 118140960795 + 475617 * 2 ^ 59
def prefixEnd_475617 : Nat := 4983230072969 + 3 ^ 40 * 475617 * 2
def baseEnd_475617 : Nat := 244220128449570880000183

theorem tailTrace_475617 : CollatzResearch.WordTrace tailWord_475617 prefixEnd_475617 244220128449570880000183 := by
  unfold tailWord_475617
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347177117928312761745105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11564784745285541841163403 17347177117928312761745105)
  ·
    refine ⟨13010382838446234571308829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17347177117928312761745105 13010382838446234571308829)
    ·
      refine ⟨4878893564417337964240811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13010382838446234571308829 4878893564417337964240811)
      ·
        refine ⟨7318340346626006946361217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878893564417337964240811 7318340346626006946361217)
        ·
          refine ⟨5488755259969505209770913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7318340346626006946361217 5488755259969505209770913)
          ·
            refine ⟨4116566444977128907328185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488755259969505209770913 4116566444977128907328185)
            ·
              refine ⟨3087424833732846680496139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116566444977128907328185 3087424833732846680496139)
              ·
                refine ⟨4631137250599270020744209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087424833732846680496139 4631137250599270020744209)
                ·
                  refine ⟨3473352937949452515558157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631137250599270020744209 3473352937949452515558157)
                  ·
                    refine ⟨1302507351731044693334309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473352937949452515558157 1302507351731044693334309)
                    ·
                      refine ⟨244220128449570880000183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1302507351731044693334309 244220128449570880000183)
                      ·
                        rfl

theorem cell23_475617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_475617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475617 prefixEnd_475617 := by exact prefixLift 475617
  have htrace : WordTrace (prefixWord ++ tailWord_475617) baseStart_475617 baseEnd_475617 := by
    simpa [prefixWord, tailWord_475617, baseEnd_475617] using wordTrace_append hprefix tailTrace_475617
  have hstable : (prefixWord ++ tailWord_475617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475617).length < 2 ^ (prefixWord ++ tailWord_475617).sum := by decide
  have hdescent : baseEnd_475617 < baseStart_475617 := by decide
  rcases family_descends (prefixWord ++ tailWord_475617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475655 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_475655 : Nat := 118140960795 + 475655 * 2 ^ 59
def prefixEnd_475655 : Nat := 4983230072969 + 3 ^ 40 * 475655 * 2
def baseEnd_475655 : Nat := 244239640714441731325009

theorem tailTrace_475655 : CollatzResearch.WordTrace tailWord_475655 prefixEnd_475655 244239640714441731325009 := by
  unfold tailWord_475655
  simp only [CollatzResearch.WordTrace]
  refine ⟨17348563091790645251628419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11565708727860430167752279 17348563091790645251628419)
  ·
    refine ⟨26022844637685967877442629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17348563091790645251628419 26022844637685967877442629)
    ·
      refine ⟨4879283369566118977020493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26022844637685967877442629 4879283369566118977020493)
      ·
        refine ⟨1829731263587294616382685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4879283369566118977020493 1829731263587294616382685)
        ·
          refine ⟨686149223845235481143507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1829731263587294616382685 686149223845235481143507)
          ·
            refine ⟨1029223835767853221715261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686149223845235481143507 1029223835767853221715261)
            ·
              refine ⟨385958938412944958143223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029223835767853221715261 385958938412944958143223)
              ·
                refine ⟨578938407619417437214835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385958938412944958143223 578938407619417437214835)
                ·
                  refine ⟨868407611429126155822253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578938407619417437214835 868407611429126155822253)
                  ·
                    refine ⟨325652854285922308433345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868407611429126155822253 325652854285922308433345)
                    ·
                      refine ⟨244239640714441731325009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325652854285922308433345 244239640714441731325009)
                      ·
                        rfl

theorem cell23_475655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_475655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475655 prefixEnd_475655 := by exact prefixLift 475655
  have htrace : WordTrace (prefixWord ++ tailWord_475655) baseStart_475655 baseEnd_475655 := by
    simpa [prefixWord, tailWord_475655, baseEnd_475655] using wordTrace_append hprefix tailTrace_475655
  have hstable : (prefixWord ++ tailWord_475655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475655).length < 2 ^ (prefixWord ++ tailWord_475655).sum := by decide
  have hdescent : baseEnd_475655 < baseStart_475655 := by decide
  rcases family_descends (prefixWord ++ tailWord_475655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475697 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_475697 : Nat := 118140960795 + 475697 * 2 ^ 59
def prefixEnd_475697 : Nat := 4983230072969 + 3 ^ 40 * 475697 * 2
def baseEnd_475697 : Nat := 244261206901930566999815

theorem tailTrace_475697 : CollatzResearch.WordTrace tailWord_475697 prefixEnd_475697 244261206901930566999815 := by
  unfold tailWord_475697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350094957638486424657345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11566729971758990949771563 17350094957638486424657345)
  ·
    refine ⟨13012571218228864818493009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17350094957638486424657345 13012571218228864818493009)
    ·
      refine ⟨9759428413671648613869757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13012571218228864818493009 9759428413671648613869757)
      ·
        refine ⟨3659785655126868230201159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9759428413671648613869757 3659785655126868230201159)
        ·
          refine ⟨5489678482690302345301739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659785655126868230201159 5489678482690302345301739)
          ·
            refine ⟨8234517724035453517952609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489678482690302345301739 8234517724035453517952609)
            ·
              refine ⟨6175888293026590138464457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234517724035453517952609 6175888293026590138464457)
              ·
                refine ⟨4631916219769942603848343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6175888293026590138464457 4631916219769942603848343)
                ·
                  refine ⟨6947874329654913905772515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631916219769942603848343 6947874329654913905772515)
                  ·
                    refine ⟨10421811494482370858658773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6947874329654913905772515 10421811494482370858658773)
                    ·
                      refine ⟨244261206901930566999815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10421811494482370858658773 244261206901930566999815)
                      ·
                        rfl

theorem cell23_475697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_475697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475697 prefixEnd_475697 := by exact prefixLift 475697
  have htrace : WordTrace (prefixWord ++ tailWord_475697) baseStart_475697 baseEnd_475697 := by
    simpa [prefixWord, tailWord_475697, baseEnd_475697] using wordTrace_append hprefix tailTrace_475697
  have hstable : (prefixWord ++ tailWord_475697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475697).length < 2 ^ (prefixWord ++ tailWord_475697).sum := by decide
  have hdescent : baseEnd_475697 < baseStart_475697 := by decide
  rcases family_descends (prefixWord ++ tailWord_475697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475718 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_475718 : Nat := 118140960795 + 475718 * 2 ^ 59
def prefixEnd_475718 : Nat := 4983230072969 + 3 ^ 40 * 475718 * 2
def baseEnd_475718 : Nat := 244271989995674984837219

theorem tailTrace_475718 : CollatzResearch.WordTrace tailWord_475718 prefixEnd_475718 244271989995674984837219 := by
  unfold tailWord_475718
  simp only [CollatzResearch.WordTrace]
  refine ⟨542214402830075219099119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11567240593708271340781205 542214402830075219099119)
  ·
    refine ⟨813321604245112828648679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542214402830075219099119 813321604245112828648679)
    ·
      refine ⟨1219982406367669242973019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813321604245112828648679 1219982406367669242973019)
      ·
        refine ⟨1829973609551503864459529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219982406367669242973019 1829973609551503864459529)
        ·
          refine ⟨1372480207163627898344647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829973609551503864459529 1372480207163627898344647)
          ·
            refine ⟨2058720310745441847516971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372480207163627898344647 2058720310745441847516971)
            ·
              refine ⟨3088080466118162771275457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058720310745441847516971 3088080466118162771275457)
              ·
                refine ⟨2316060349588622078456593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088080466118162771275457 2316060349588622078456593)
                ·
                  refine ⟨1737045262191466558842445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316060349588622078456593 1737045262191466558842445)
                  ·
                    refine ⟨651391973321799959565917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737045262191466558842445 651391973321799959565917)
                    ·
                      refine ⟨244271989995674984837219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651391973321799959565917 244271989995674984837219)
                      ·
                        rfl

theorem cell23_475718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_475718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475718 prefixEnd_475718 := by exact prefixLift 475718
  have htrace : WordTrace (prefixWord ++ tailWord_475718) baseStart_475718 baseEnd_475718 := by
    simpa [prefixWord, tailWord_475718, baseEnd_475718] using wordTrace_append hprefix tailTrace_475718
  have hstable : (prefixWord ++ tailWord_475718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475718).length < 2 ^ (prefixWord ++ tailWord_475718).sum := by decide
  have hdescent : baseEnd_475718 < baseStart_475718 := by decide
  rcases family_descends (prefixWord ++ tailWord_475718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475724 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_475724 : Nat := 118140960795 + 475724 * 2 ^ 59
def prefixEnd_475724 : Nat := 4983230072969 + 3 ^ 40 * 475724 * 2
def baseEnd_475724 : Nat := 244275070879601961362191

theorem tailTrace_475724 : CollatzResearch.WordTrace tailWord_475724 prefixEnd_475724 244275070879601961362191 := by
  unfold tailWord_475724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675539864270335017945113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11567386485693780023926817 8675539864270335017945113)
  ·
    refine ⟨6506654898202751263458835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8675539864270335017945113 6506654898202751263458835)
    ·
      refine ⟨9759982347304126895188253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6506654898202751263458835 9759982347304126895188253)
      ·
        refine ⟨3659993380239047585695595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9759982347304126895188253 3659993380239047585695595)
        ·
          refine ⟨5489990070358571378543393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659993380239047585695595 5489990070358571378543393)
          ·
            refine ⟨4117492552768928533907545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489990070358571378543393 4117492552768928533907545)
            ·
              refine ⟨3088119414576696400430659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117492552768928533907545 3088119414576696400430659)
              ·
                refine ⟨4632179121865044600645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088119414576696400430659 4632179121865044600645989)
                ·
                  refine ⟨868533585349695862621123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4632179121865044600645989 868533585349695862621123)
                  ·
                    refine ⟨1302800378024543793931685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868533585349695862621123 1302800378024543793931685)
                    ·
                      refine ⟨244275070879601961362191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1302800378024543793931685 244275070879601961362191)
                      ·
                        rfl

theorem cell23_475724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_475724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475724 prefixEnd_475724 := by exact prefixLift 475724
  have htrace : WordTrace (prefixWord ++ tailWord_475724) baseStart_475724 baseEnd_475724 := by
    simpa [prefixWord, tailWord_475724, baseEnd_475724] using wordTrace_append hprefix tailTrace_475724
  have hstable : (prefixWord ++ tailWord_475724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475724).length < 2 ^ (prefixWord ++ tailWord_475724).sum := by decide
  have hdescent : baseEnd_475724 < baseStart_475724 := by decide
  rcases family_descends (prefixWord ++ tailWord_475724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475727 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_475727 : Nat := 118140960795 + 475727 * 2 ^ 59
def prefixEnd_475727 : Nat := 4983230072969 + 3 ^ 40 * 475727 * 2
def baseEnd_475727 : Nat := 244276611321565449624677

theorem tailTrace_475727 : CollatzResearch.WordTrace tailWord_475727 prefixEnd_475727 244276611321565449624677 := by
  unfold tailWord_475727
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351189147529801548249435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11567459431686534365499623 17351189147529801548249435)
  ·
    refine ⟨26026783721294702322374153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351189147529801548249435 26026783721294702322374153)
    ·
      refine ⟨19520087790971026741780615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26026783721294702322374153 19520087790971026741780615)
      ·
        refine ⟨29280131686456540112670923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520087790971026741780615 29280131686456540112670923)
        ·
          refine ⟨43920197529684810169006385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29280131686456540112670923 43920197529684810169006385)
          ·
            refine ⟨32940148147263607626754789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43920197529684810169006385 32940148147263607626754789)
            ·
              refine ⟨6176277777611926430016523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32940148147263607626754789 6176277777611926430016523)
              ·
                refine ⟨9264416666417889645024785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176277777611926430016523 9264416666417889645024785)
                ·
                  refine ⟨6948312499813417233768589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264416666417889645024785 6948312499813417233768589)
                  ·
                    refine ⟨2605617187430031462663221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6948312499813417233768589 2605617187430031462663221)
                    ·
                      refine ⟨244276611321565449624677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2605617187430031462663221 244276611321565449624677)
                      ·
                        rfl

theorem cell23_475727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_475727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475727 prefixEnd_475727 := by exact prefixLift 475727
  have htrace : WordTrace (prefixWord ++ tailWord_475727) baseStart_475727 baseEnd_475727 := by
    simpa [prefixWord, tailWord_475727, baseEnd_475727] using wordTrace_append hprefix tailTrace_475727
  have hstable : (prefixWord ++ tailWord_475727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475727).length < 2 ^ (prefixWord ++ tailWord_475727).sum := by decide
  have hdescent : baseEnd_475727 < baseStart_475727 := by decide
  rcases family_descends (prefixWord ++ tailWord_475727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475744 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_475744 : Nat := 118140960795 + 475744 * 2 ^ 59
def prefixEnd_475744 : Nat := 4983230072969 + 3 ^ 40 * 475744 * 2
def baseEnd_475744 : Nat := 244285340492691883112099

theorem tailTrace_475744 : CollatzResearch.WordTrace tailWord_475744 prefixEnd_475744 244285340492691883112099 := by
  unfold tailWord_475744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675904594234106725809143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11567872792312142301078857 8675904594234106725809143)
  ·
    refine ⟨13013856891351160088713715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8675904594234106725809143 13013856891351160088713715)
    ·
      refine ⟨19520785337026740133070573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013856891351160088713715 19520785337026740133070573)
      ·
        refine ⟨7320294501385027549901465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19520785337026740133070573 7320294501385027549901465)
        ·
          refine ⟨5490220876038770662426099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7320294501385027549901465 5490220876038770662426099)
          ·
            refine ⟨8235331314058155993639149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490220876038770662426099 8235331314058155993639149)
            ·
              refine ⟨3088249242771808497614681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8235331314058155993639149 3088249242771808497614681)
              ·
                refine ⟨2316186932078856373211011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088249242771808497614681 2316186932078856373211011)
                ·
                  refine ⟨3474280398118284559816517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316186932078856373211011 3474280398118284559816517)
                  ·
                    refine ⟨651427574647178354965597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3474280398118284559816517 651427574647178354965597)
                    ·
                      refine ⟨244285340492691883112099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651427574647178354965597 244285340492691883112099)
                      ·
                        rfl

theorem cell23_475744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_475744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475744 prefixEnd_475744 := by exact prefixLift 475744
  have htrace : WordTrace (prefixWord ++ tailWord_475744) baseStart_475744 baseEnd_475744 := by
    simpa [prefixWord, tailWord_475744, baseEnd_475744] using wordTrace_append hprefix tailTrace_475744
  have hstable : (prefixWord ++ tailWord_475744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475744).length < 2 ^ (prefixWord ++ tailWord_475744).sum := by decide
  have hdescent : baseEnd_475744 < baseStart_475744 := by decide
  rcases family_descends (prefixWord ++ tailWord_475744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475754 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_475754 : Nat := 118140960795 + 475754 * 2 ^ 59
def prefixEnd_475754 : Nat := 4983230072969 + 3 ^ 40 * 475754 * 2
def baseEnd_475754 : Nat := 244290475299236843987053

theorem tailTrace_475754 : CollatzResearch.WordTrace tailWord_475754 prefixEnd_475754 244290475299236843987053 := by
  unfold tailWord_475754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338043479607996289870579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11568115945621323439654877 4338043479607996289870579)
  ·
    refine ⟨6507065219411994434805869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4338043479607996289870579 6507065219411994434805869)
    ·
      refine ⟨2440149457279497913052201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6507065219411994434805869 2440149457279497913052201)
      ·
        refine ⟨1830112092959623434789151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440149457279497913052201 1830112092959623434789151)
        ·
          refine ⟨2745168139439435152183727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830112092959623434789151 2745168139439435152183727)
          ·
            refine ⟨4117752209159152728275591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745168139439435152183727 4117752209159152728275591)
            ·
              refine ⟨6176628313738729092413387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117752209159152728275591 6176628313738729092413387)
              ·
                refine ⟨9264942470608093638620081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176628313738729092413387 9264942470608093638620081)
                ·
                  refine ⟨6948706852956070228965061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264942470608093638620081 6948706852956070228965061)
                  ·
                    refine ⟨1302882534929263167930949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948706852956070228965061 1302882534929263167930949)
                    ·
                      refine ⟨244290475299236843987053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1302882534929263167930949 244290475299236843987053)
                      ·
                        rfl

theorem cell23_475754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_475754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475754 prefixEnd_475754 := by exact prefixLift 475754
  have htrace : WordTrace (prefixWord ++ tailWord_475754) baseStart_475754 baseEnd_475754 := by
    simpa [prefixWord, tailWord_475754, baseEnd_475754] using wordTrace_append hprefix tailTrace_475754
  have hstable : (prefixWord ++ tailWord_475754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475754).length < 2 ^ (prefixWord ++ tailWord_475754).sum := by decide
  have hdescent : baseEnd_475754 < baseStart_475754 := by decide
  rcases family_descends (prefixWord ++ tailWord_475754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475801 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 4, 3, 2]
def baseStart_475801 : Nat := 118140960795 + 475801 * 2 ^ 59
def prefixEnd_475801 : Nat := 4983230072969 + 3 ^ 40 * 475801 * 2
def baseEnd_475801 : Nat := 244314608889998160099337

theorem tailTrace_475801 : CollatzResearch.WordTrace tailWord_475801 prefixEnd_475801 244314608889998160099337 := by
  unfold tailWord_475801
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353888149261712186443257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11569258766174474790962171 17353888149261712186443257)
  ·
    refine ⟨13015416111946284139832443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17353888149261712186443257 13015416111946284139832443)
    ·
      refine ⟨19523124167919426209748665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015416111946284139832443 19523124167919426209748665)
      ·
        refine ⟨14642343125939569657311499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19523124167919426209748665 14642343125939569657311499)
        ·
          refine ⟨21963514688909354485967249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642343125939569657311499 21963514688909354485967249)
          ·
            refine ⟨16472636016682015864475437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21963514688909354485967249 16472636016682015864475437)
            ·
              refine ⟨6177238506255755949178289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16472636016682015864475437 6177238506255755949178289)
              ·
                refine ⟨4632928879691816961883717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177238506255755949178289 4632928879691816961883717)
                ·
                  refine ⟨868674164942215680353197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4632928879691816961883717 868674164942215680353197)
                  ·
                    refine ⟨325752811853330880132449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868674164942215680353197 325752811853330880132449)
                    ·
                      refine ⟨244314608889998160099337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325752811853330880132449 244314608889998160099337)
                      ·
                        rfl

theorem cell23_475801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_475801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475801 prefixEnd_475801 := by exact prefixLift 475801
  have htrace : WordTrace (prefixWord ++ tailWord_475801) baseStart_475801 baseEnd_475801 := by
    simpa [prefixWord, tailWord_475801, baseEnd_475801] using wordTrace_append hprefix tailTrace_475801
  have hstable : (prefixWord ++ tailWord_475801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475801).length < 2 ^ (prefixWord ++ tailWord_475801).sum := by decide
  have hdescent : baseEnd_475801 < baseStart_475801 := by decide
  rcases family_descends (prefixWord ++ tailWord_475801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475858 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_475858 : Nat := 118140960795 + 475858 * 2 ^ 59
def prefixEnd_475858 : Nat := 4983230072969 + 3 ^ 40 * 475858 * 2
def baseEnd_475858 : Nat := 81447959095768145695525

theorem tailTrace_475858 : CollatzResearch.WordTrace tailWord_475858 prefixEnd_475858 81447959095768145695525 := by
  unfold tailWord_475858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338991777513802730317057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11570644740036807280845485 4338991777513802730317057)
  ·
    refine ⟨3254243833135352047737793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4338991777513802730317057 3254243833135352047737793)
    ·
      refine ⟨2440682874851514035803345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3254243833135352047737793 2440682874851514035803345)
      ·
        refine ⟨1830512156138635526852509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440682874851514035803345 1830512156138635526852509)
        ·
          refine ⟨686442058551988322569691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1830512156138635526852509 686442058551988322569691)
          ·
            refine ⟨1029663087827982483854537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686442058551988322569691 1029663087827982483854537)
            ·
              refine ⟨772247315870986862890903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029663087827982483854537 772247315870986862890903)
              ·
                refine ⟨1158370973806480294336355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772247315870986862890903 1158370973806480294336355)
                ·
                  refine ⟨1737556460709720441504533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158370973806480294336355 1737556460709720441504533)
                  ·
                    refine ⟨81447959095768145695525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1737556460709720441504533 81447959095768145695525)
                    ·
                      rfl

theorem cell23_475858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_475858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475858 prefixEnd_475858 := by exact prefixLift 475858
  have htrace : WordTrace (prefixWord ++ tailWord_475858) baseStart_475858 baseEnd_475858 := by
    simpa [prefixWord, tailWord_475858, baseEnd_475858] using wordTrace_append hprefix tailTrace_475858
  have hstable : (prefixWord ++ tailWord_475858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475858).length < 2 ^ (prefixWord ++ tailWord_475858).sum := by decide
  have hdescent : baseEnd_475858 < baseStart_475858 := by decide
  rcases family_descends (prefixWord ++ tailWord_475858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475871 : List Nat := [1, 1, 2, 3, 2, 4, 3, 7]
def baseStart_475871 : Nat := 118140960795 + 475871 * 2 ^ 59
def prefixEnd_475871 : Nat := 4983230072969 + 3 ^ 40 * 475871 * 2
def baseEnd_475871 : Nat := 9050020464289366156445

theorem tailTrace_475871 : CollatzResearch.WordTrace tailWord_475871 prefixEnd_475871 9050020464289366156445 := by
  unfold tailWord_475871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356441259008114141491467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11570960839338742760994311 17356441259008114141491467)
  ·
    refine ⟨26034661888512171212237201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17356441259008114141491467 26034661888512171212237201)
    ·
      refine ⟨19525996416384128409177901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26034661888512171212237201 19525996416384128409177901)
      ·
        refine ⟨7322248656144048153441713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19525996416384128409177901 7322248656144048153441713)
        ·
          refine ⟨5491686492108036115081285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7322248656144048153441713 5491686492108036115081285)
          ·
            refine ⟨1029691217270256771577741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5491686492108036115081285 1029691217270256771577741)
            ·
              refine ⟨386134206476346289341653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029691217270256771577741 386134206476346289341653)
              ·
                refine ⟨9050020464289366156445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386134206476346289341653 9050020464289366156445)
                ·
                  rfl

theorem cell23_475871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 7].length) (baseStart_475871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475871 prefixEnd_475871 := by exact prefixLift 475871
  have htrace : WordTrace (prefixWord ++ tailWord_475871) baseStart_475871 baseEnd_475871 := by
    simpa [prefixWord, tailWord_475871, baseEnd_475871] using wordTrace_append hprefix tailTrace_475871
  have hstable : (prefixWord ++ tailWord_475871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475871).length < 2 ^ (prefixWord ++ tailWord_475871).sum := by decide
  have hdescent : baseEnd_475871 < baseStart_475871 := by decide
  rcases family_descends (prefixWord ++ tailWord_475871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475881 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_475881 : Nat := 118140960795 + 475881 * 2 ^ 59
def prefixEnd_475881 : Nat := 4983230072969 + 3 ^ 40 * 475881 * 2
def baseEnd_475881 : Nat := 244355687342357847098969

theorem tailTrace_475881 : CollatzResearch.WordTrace tailWord_475881 prefixEnd_475881 244355687342357847098969 := by
  unfold tailWord_475881
  simp only [CollatzResearch.WordTrace]
  refine ⟨17356805988971885849355497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11571203992647923899570331 17356805988971885849355497)
  ·
    refine ⟨13017604491728914387016623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17356805988971885849355497 13017604491728914387016623)
    ·
      refine ⟨19526406737593371580524935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13017604491728914387016623 19526406737593371580524935)
      ·
        refine ⟨29289610106390057370787403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19526406737593371580524935 29289610106390057370787403)
        ·
          refine ⟨43934415159585086056181105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29289610106390057370787403 43934415159585086056181105)
          ·
            refine ⟨32950811369688814542135829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43934415159585086056181105 32950811369688814542135829)
            ·
              refine ⟨1544569282954163181662617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32950811369688814542135829 1544569282954163181662617)
              ·
                refine ⟨1158426962215622386246963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544569282954163181662617 1158426962215622386246963)
                ·
                  refine ⟨1737640443323433579370445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158426962215622386246963 1737640443323433579370445)
                  ·
                    refine ⟨651615166246287592263917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1737640443323433579370445 651615166246287592263917)
                    ·
                      refine ⟨244355687342357847098969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651615166246287592263917 244355687342357847098969)
                      ·
                        rfl

theorem cell23_475881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_475881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475881 prefixEnd_475881 := by exact prefixLift 475881
  have htrace : WordTrace (prefixWord ++ tailWord_475881) baseStart_475881 baseEnd_475881 := by
    simpa [prefixWord, tailWord_475881, baseEnd_475881] using wordTrace_append hprefix tailTrace_475881
  have hstable : (prefixWord ++ tailWord_475881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475881).length < 2 ^ (prefixWord ++ tailWord_475881).sum := by decide
  have hdescent : baseEnd_475881 < baseStart_475881 := by decide
  rcases family_descends (prefixWord ++ tailWord_475881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475892 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_475892 : Nat := 118140960795 + 475892 * 2 ^ 59
def prefixEnd_475892 : Nat := 4983230072969 + 3 ^ 40 * 475892 * 2
def baseEnd_475892 : Nat := 81453778543185768020473

theorem tailTrace_475892 : CollatzResearch.WordTrace tailWord_475892 prefixEnd_475892 81453778543185768020473 := by
  unfold tailWord_475892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678603595966017364002965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11571471461288023152003953 8678603595966017364002965)
  ·
    refine ⟨406809543560907063937639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8678603595966017364002965 406809543560907063937639)
    ·
      refine ⟨610214315341360595906459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406809543560907063937639 610214315341360595906459)
      ·
        refine ⟨915321473012040893859689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610214315341360595906459 915321473012040893859689)
        ·
          refine ⟨686491104759030670394767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915321473012040893859689 686491104759030670394767)
          ·
            refine ⟨1029736657138546005592151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686491104759030670394767 1029736657138546005592151)
            ·
              refine ⟨1544604985707819008388227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029736657138546005592151 1544604985707819008388227)
              ·
                refine ⟨2316907478561728512582341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544604985707819008388227 2316907478561728512582341)
                ·
                  refine ⟨434420152230324096109189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2316907478561728512582341 434420152230324096109189)
                  ·
                    refine ⟨81453778543185768020473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434420152230324096109189 81453778543185768020473)
                    ·
                      rfl

theorem cell23_475892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_475892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475892 prefixEnd_475892 := by exact prefixLift 475892
  have htrace : WordTrace (prefixWord ++ tailWord_475892) baseStart_475892 baseEnd_475892 := by
    simpa [prefixWord, tailWord_475892, baseEnd_475892] using wordTrace_append hprefix tailTrace_475892
  have hstable : (prefixWord ++ tailWord_475892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475892).length < 2 ^ (prefixWord ++ tailWord_475892).sum := by decide
  have hdescent : baseEnd_475892 < baseStart_475892 := by decide
  rcases family_descends (prefixWord ++ tailWord_475892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475922 : List Nat := [3, 2, 4, 1, 3, 1, 2, 7]
def baseStart_475922 : Nat := 118140960795 + 475922 * 2 ^ 59
def prefixEnd_475922 : Nat := 4983230072969 + 3 ^ 40 * 475922 * 2
def baseEnd_475922 : Nat := 9050990372192303210603

theorem tailTrace_475922 : CollatzResearch.WordTrace tailWord_475922 prefixEnd_475922 9050990372192303210603 := by
  unfold tailWord_475922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339575345455837462899505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11572200921215566567732013 4339575345455837462899505)
  ·
    refine ⟨3254681509091878097174629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4339575345455837462899505 3254681509091878097174629)
    ·
      refine ⟨610252782954727143220243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3254681509091878097174629 610252782954727143220243)
      ·
        refine ⟨915379174432090714830365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610252782954727143220243 915379174432090714830365)
        ·
          refine ⟨343267190412034018061387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915379174432090714830365 343267190412034018061387)
          ·
            refine ⟨514900785618051027092081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343267190412034018061387 514900785618051027092081)
            ·
              refine ⟨386175589213538270319061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514900785618051027092081 386175589213538270319061)
              ·
                refine ⟨9050990372192303210603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386175589213538270319061 9050990372192303210603)
                ·
                  rfl

theorem cell23_475922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_475922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475922 prefixEnd_475922 := by exact prefixLift 475922
  have htrace : WordTrace (prefixWord ++ tailWord_475922) baseStart_475922 baseEnd_475922 := by
    simpa [prefixWord, tailWord_475922, baseEnd_475922] using wordTrace_append hprefix tailTrace_475922
  have hstable : (prefixWord ++ tailWord_475922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475922).length < 2 ^ (prefixWord ++ tailWord_475922).sum := by decide
  have hdescent : baseEnd_475922 < baseStart_475922 := by decide
  rcases family_descends (prefixWord ++ tailWord_475922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475925 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_475925 : Nat := 118140960795 + 475925 * 2 ^ 59
def prefixEnd_475925 : Nat := 4983230072969 + 3 ^ 40 * 475925 * 2
def baseEnd_475925 : Nat := 244378280491155674948767

theorem tailTrace_475925 : CollatzResearch.WordTrace tailWord_475925 prefixEnd_475925 244378280491155674948767 := by
  unfold tailWord_475925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358410800812481363957229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11572273867208320909304819 17358410800812481363957229)
  ·
    refine ⟨6509404050304680511483961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17358410800812481363957229 6509404050304680511483961)
    ·
      refine ⟨4882053037728510383612971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509404050304680511483961 4882053037728510383612971)
      ·
        refine ⟨7323079556592765575419457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882053037728510383612971 7323079556592765575419457)
        ·
          refine ⟨5492309667444574181564593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7323079556592765575419457 5492309667444574181564593)
          ·
            refine ⟨4119232250583430636173445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492309667444574181564593 4119232250583430636173445)
            ·
              refine ⟨772356046984393244282521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4119232250583430636173445 772356046984393244282521)
              ·
                refine ⟨579267035238294933211891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772356046984393244282521 579267035238294933211891)
                ·
                  refine ⟨868900552857442399817837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579267035238294933211891 868900552857442399817837)
                  ·
                    refine ⟨325837707321540899931689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868900552857442399817837 325837707321540899931689)
                    ·
                      refine ⟨244378280491155674948767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325837707321540899931689 244378280491155674948767)
                      ·
                        rfl

theorem cell23_475925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_475925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475925 prefixEnd_475925 := by exact prefixLift 475925
  have htrace : WordTrace (prefixWord ++ tailWord_475925) baseStart_475925 baseEnd_475925 := by
    simpa [prefixWord, tailWord_475925, baseEnd_475925] using wordTrace_append hprefix tailTrace_475925
  have hstable : (prefixWord ++ tailWord_475925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475925).length < 2 ^ (prefixWord ++ tailWord_475925).sum := by decide
  have hdescent : baseEnd_475925 < baseStart_475925 := by decide
  rcases family_descends (prefixWord ++ tailWord_475925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475933 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_475933 : Nat := 118140960795 + 475933 * 2 ^ 59
def prefixEnd_475933 : Nat := 4983230072969 + 3 ^ 40 * 475933 * 2
def baseEnd_475933 : Nat := 244382388336391643648731

theorem tailTrace_475933 : CollatzResearch.WordTrace tailWord_475933 prefixEnd_475933 244382388336391643648731 := by
  unfold tailWord_475933
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358702584783498730248453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11572468389855665820165635 17358702584783498730248453)
  ·
    refine ⟨3254756734646906011921585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17358702584783498730248453 3254756734646906011921585)
    ·
      refine ⟨2441067550985179508941189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3254756734646906011921585 2441067550985179508941189)
      ·
        refine ⟨457700165809721157926473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2441067550985179508941189 457700165809721157926473)
        ·
          refine ⟨343275124357290868444855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457700165809721157926473 343275124357290868444855)
          ·
            refine ⟨514912686535936302667283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343275124357290868444855 514912686535936302667283)
            ·
              refine ⟨772369029803904454000925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514912686535936302667283 772369029803904454000925)
              ·
                refine ⟨289638386176464170250347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772369029803904454000925 289638386176464170250347)
                ·
                  refine ⟨434457579264696255375521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289638386176464170250347 434457579264696255375521)
                  ·
                    refine ⟨325843184448522191531641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 434457579264696255375521 325843184448522191531641)
                    ·
                      refine ⟨244382388336391643648731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325843184448522191531641 244382388336391643648731)
                      ·
                        rfl

theorem cell23_475933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_475933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475933 prefixEnd_475933 := by exact prefixLift 475933
  have htrace : WordTrace (prefixWord ++ tailWord_475933) baseStart_475933 baseEnd_475933 := by
    simpa [prefixWord, tailWord_475933, baseEnd_475933] using wordTrace_append hprefix tailTrace_475933
  have hstable : (prefixWord ++ tailWord_475933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475933).length < 2 ^ (prefixWord ++ tailWord_475933).sum := by decide
  have hdescent : baseEnd_475933 < baseStart_475933 := by decide
  rcases family_descends (prefixWord ++ tailWord_475933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475941 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_475941 : Nat := 118140960795 + 475941 * 2 ^ 59
def prefixEnd_475941 : Nat := 4983230072969 + 3 ^ 40 * 475941 * 2
def baseEnd_475941 : Nat := 244386496181627612348693

theorem tailTrace_475941 : CollatzResearch.WordTrace tailWord_475941 prefixEnd_475941 244386496181627612348693 := by
  unfold tailWord_475941
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358994368754516096539677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11572662912503010731026451 17358994368754516096539677)
  ·
    refine ⟨6509622888282943536202379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17358994368754516096539677 6509622888282943536202379)
    ·
      refine ⟨9764434332424415304303569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509622888282943536202379 9764434332424415304303569)
      ·
        refine ⟨7323325749318311478227677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9764434332424415304303569 7323325749318311478227677)
        ·
          refine ⟨2746247155994366804335379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7323325749318311478227677 2746247155994366804335379)
          ·
            refine ⟨4119370733991550206503069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746247155994366804335379 4119370733991550206503069)
            ·
              refine ⟨1544764025246831327438651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4119370733991550206503069 1544764025246831327438651)
              ·
                refine ⟨2317146037870246991157977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544764025246831327438651 2317146037870246991157977)
                ·
                  refine ⟨1737859528402685243368483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317146037870246991157977 1737859528402685243368483)
                  ·
                    refine ⟨2606789292604027865052725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737859528402685243368483 2606789292604027865052725)
                    ·
                      refine ⟨244386496181627612348693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2606789292604027865052725 244386496181627612348693)
                      ·
                        rfl

theorem cell23_475941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_475941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475941 prefixEnd_475941 := by exact prefixLift 475941
  have htrace : WordTrace (prefixWord ++ tailWord_475941) baseStart_475941 baseEnd_475941 := by
    simpa [prefixWord, tailWord_475941, baseEnd_475941] using wordTrace_append hprefix tailTrace_475941
  have hstable : (prefixWord ++ tailWord_475941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475941).length < 2 ^ (prefixWord ++ tailWord_475941).sum := by decide
  have hdescent : baseEnd_475941 < baseStart_475941 := by decide
  rcases family_descends (prefixWord ++ tailWord_475941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475955 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 4, 2, 2]
def baseStart_475955 : Nat := 118140960795 + 475955 * 2 ^ 59
def prefixEnd_475955 : Nat := 4983230072969 + 3 ^ 40 * 475955 * 2
def baseEnd_475955 : Nat := 244393684910790557573629

theorem tailTrace_475955 : CollatzResearch.WordTrace tailWord_475955 prefixEnd_475955 244393684910790557573629 := by
  unfold tailWord_475955
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359504990703796487549319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11573003327135864325032879 17359504990703796487549319)
  ·
    refine ⟨26039257486055694731323979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17359504990703796487549319 26039257486055694731323979)
    ·
      refine ⟨39058886229083542096985969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26039257486055694731323979 39058886229083542096985969)
      ·
        refine ⟨29294164671812656572739477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39058886229083542096985969 29294164671812656572739477)
        ·
          refine ⟨1373163968991218276847163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29294164671812656572739477 1373163968991218276847163)
          ·
            refine ⟨2059745953486827415270745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373163968991218276847163 2059745953486827415270745)
            ·
              refine ⟨1544809465115120561453059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059745953486827415270745 1544809465115120561453059)
              ·
                refine ⟨2317214197672680842179589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544809465115120561453059 2317214197672680842179589)
                ·
                  refine ⟨434477662063627657908673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317214197672680842179589 434477662063627657908673)
                  ·
                    refine ⟨325858246547720743431505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 434477662063627657908673 325858246547720743431505)
                    ·
                      refine ⟨244393684910790557573629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325858246547720743431505 244393684910790557573629)
                      ·
                        rfl

theorem cell23_475955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2, 2].length) (baseStart_475955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475955 prefixEnd_475955 := by exact prefixLift 475955
  have htrace : WordTrace (prefixWord ++ tailWord_475955) baseStart_475955 baseEnd_475955 := by
    simpa [prefixWord, tailWord_475955, baseEnd_475955] using wordTrace_append hprefix tailTrace_475955
  have hstable : (prefixWord ++ tailWord_475955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475955).length < 2 ^ (prefixWord ++ tailWord_475955).sum := by decide
  have hdescent : baseEnd_475955 < baseStart_475955 := by decide
  rcases family_descends (prefixWord ++ tailWord_475955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475966 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_475966 : Nat := 118140960795 + 475966 * 2 ^ 59
def prefixEnd_475966 : Nat := 4983230072969 + 3 ^ 40 * 475966 * 2
def baseEnd_475966 : Nat := 244399333197990014536079

theorem tailTrace_475966 : CollatzResearch.WordTrace tailWord_475966 prefixEnd_475966 244399333197990014536079 := by
  unfold tailWord_475966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169988274207993170774969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11573270795775963577466501 2169988274207993170774969)
  ·
    refine ⟨1627491205655994878081227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169988274207993170774969 1627491205655994878081227)
    ·
      refine ⟨2441236808483992317121841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627491205655994878081227 2441236808483992317121841)
      ·
        refine ⟨1830927606362994237841381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441236808483992317121841 1830927606362994237841381)
        ·
          refine ⟨343298926193061419595259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1830927606362994237841381 343298926193061419595259)
          ·
            refine ⟨514948389289592129392889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343298926193061419595259 514948389289592129392889)
            ·
              refine ⟨386211291967194097044667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514948389289592129392889 386211291967194097044667)
              ·
                refine ⟨579316937950791145567001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386211291967194097044667 579316937950791145567001)
                ·
                  refine ⟨434487703463093359175251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579316937950791145567001 434487703463093359175251)
                  ·
                    refine ⟨651731555194640038762877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434487703463093359175251 651731555194640038762877)
                    ·
                      refine ⟨244399333197990014536079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651731555194640038762877 244399333197990014536079)
                      ·
                        rfl

theorem cell23_475966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_475966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475966 prefixEnd_475966 := by exact prefixLift 475966
  have htrace : WordTrace (prefixWord ++ tailWord_475966) baseStart_475966 baseEnd_475966 := by
    simpa [prefixWord, tailWord_475966, baseEnd_475966] using wordTrace_append hprefix tailTrace_475966
  have hstable : (prefixWord ++ tailWord_475966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475966).length < 2 ^ (prefixWord ++ tailWord_475966).sum := by decide
  have hdescent : baseEnd_475966 < baseStart_475966 := by decide
  rcases family_descends (prefixWord ++ tailWord_475966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475971 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3]
def baseStart_475971 : Nat := 118140960795 + 475971 * 2 ^ 59
def prefixEnd_475971 : Nat := 4983230072969 + 3 ^ 40 * 475971 * 2
def baseEnd_475971 : Nat := 244401900601262494973555

theorem tailTrace_475971 : CollatzResearch.WordTrace tailWord_475971 prefixEnd_475971 244401900601262494973555 := by
  unfold tailWord_475971
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360088558645831220131767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11573392372430554146754511 17360088558645831220131767)
  ·
    refine ⟨26040132837968746830197651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17360088558645831220131767 26040132837968746830197651)
    ·
      refine ⟨39060199256953120245296477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26040132837968746830197651 39060199256953120245296477)
      ·
        refine ⟨14647574721357420091986179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39060199256953120245296477 14647574721357420091986179)
        ·
          refine ⟨21971362082036130137979269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14647574721357420091986179 21971362082036130137979269)
          ·
            refine ⟨4119630390381774400871113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21971362082036130137979269 4119630390381774400871113)
            ·
              refine ⟨3089722792786330800653335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119630390381774400871113 3089722792786330800653335)
              ·
                refine ⟨4634584189179496200980003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089722792786330800653335 4634584189179496200980003)
                ·
                  refine ⟨6951876283769244301470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634584189179496200980003 6951876283769244301470005)
                  ·
                    refine ⟨651738401603366653262813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6951876283769244301470005 651738401603366653262813)
                    ·
                      refine ⟨244401900601262494973555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 651738401603366653262813 244401900601262494973555)
                      ·
                        rfl

theorem cell23_475971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_475971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_475971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_475971 prefixEnd_475971 := by exact prefixLift 475971
  have htrace : WordTrace (prefixWord ++ tailWord_475971) baseStart_475971 baseEnd_475971 := by
    simpa [prefixWord, tailWord_475971, baseEnd_475971] using wordTrace_append hprefix tailTrace_475971
  have hstable : (prefixWord ++ tailWord_475971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475971).length < 2 ^ (prefixWord ++ tailWord_475971).sum := by decide
  have hdescent : baseEnd_475971 < baseStart_475971 := by decide
  rcases family_descends (prefixWord ++ tailWord_475971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476008 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_476008 : Nat := 118140960795 + 476008 * 2 ^ 59
def prefixEnd_476008 : Nat := 4983230072969 + 3 ^ 40 * 476008 * 2
def baseEnd_476008 : Nat := 81473633128492950070295

theorem tailTrace_476008 : CollatzResearch.WordTrace tailWord_476008 prefixEnd_476008 81473633128492950070295 := by
  unfold tailWord_476008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680719029755893269614339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11574292039674524359485785 8680719029755893269614339)
  ·
    refine ⟨13021078544633839904421509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680719029755893269614339 13021078544633839904421509)
    ·
      refine ⟨2441452227118844982079033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13021078544633839904421509 2441452227118844982079033)
      ·
        refine ⟨1831089170339133736559275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441452227118844982079033 1831089170339133736559275)
        ·
          refine ⟨2746633755508700604838913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831089170339133736559275 2746633755508700604838913)
          ·
            refine ⟨2059975316631525453629185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746633755508700604838913 2059975316631525453629185)
            ·
              refine ⟨1544981487473644090221889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059975316631525453629185 1544981487473644090221889)
              ·
                refine ⟨1158736115605233067666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544981487473644090221889 1158736115605233067666417)
                ·
                  refine ⟨869052086703924800749813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158736115605233067666417 869052086703924800749813)
                  ·
                    refine ⟨81473633128492950070295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 869052086703924800749813 81473633128492950070295)
                    ·
                      rfl

theorem cell23_476008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_476008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476008 prefixEnd_476008 := by exact prefixLift 476008
  have htrace : WordTrace (prefixWord ++ tailWord_476008) baseStart_476008 baseEnd_476008 := by
    simpa [prefixWord, tailWord_476008, baseEnd_476008] using wordTrace_append hprefix tailTrace_476008
  have hstable : (prefixWord ++ tailWord_476008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476008).length < 2 ^ (prefixWord ++ tailWord_476008).sum := by decide
  have hdescent : baseEnd_476008 < baseStart_476008 := by decide
  rcases family_descends (prefixWord ++ tailWord_476008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476085 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 6]
def baseStart_476085 : Nat := 118140960795 + 476085 * 2 ^ 59
def prefixEnd_476085 : Nat := 4983230072969 + 3 ^ 40 * 476085 * 2
def baseEnd_476085 : Nat := 27162270821763894327559

theorem tailTrace_476085 : CollatzResearch.WordTrace tailWord_476085 prefixEnd_476085 27162270821763894327559 := by
  unfold tailWord_476085
  simp only [CollatzResearch.WordTrace]
  refine ⟨17364246480232828689781709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11576164320155219126521139 17364246480232828689781709)
  ·
    refine ⟨6511592430087310758668141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17364246480232828689781709 6511592430087310758668141)
    ·
      refine ⟨2441847161282741534500553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6511592430087310758668141 2441847161282741534500553)
      ·
        refine ⟨1831385370962056150875415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441847161282741534500553 1831385370962056150875415)
        ·
          refine ⟨2747078056443084226313123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831385370962056150875415 2747078056443084226313123)
          ·
            refine ⟨4120617084664626339469685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747078056443084226313123 4120617084664626339469685)
            ·
              refine ⟨386307851687308719325283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4120617084664626339469685 386307851687308719325283)
              ·
                refine ⟨579461777530963078987925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386307851687308719325283 579461777530963078987925)
                ·
                  refine ⟨27162270821763894327559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 579461777530963078987925 27162270821763894327559)
                  ·
                    rfl

theorem cell23_476085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_476085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476085 prefixEnd_476085 := by exact prefixLift 476085
  have htrace : WordTrace (prefixWord ++ tailWord_476085) baseStart_476085 baseEnd_476085 := by
    simpa [prefixWord, tailWord_476085, baseEnd_476085] using wordTrace_append hprefix tailTrace_476085
  have hstable : (prefixWord ++ tailWord_476085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476085).length < 2 ^ (prefixWord ++ tailWord_476085).sum := by decide
  have hdescent : baseEnd_476085 < baseStart_476085 := by decide
  rcases family_descends (prefixWord ++ tailWord_476085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476122 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2]
def baseStart_476122 : Nat := 118140960795 + 476122 * 2 ^ 59
def prefixEnd_476122 : Nat := 4983230072969 + 3 ^ 40 * 476122 * 2
def baseEnd_476122 : Nat := 244479436180091404185361

theorem tailTrace_476122 : CollatzResearch.WordTrace tailWord_476122 prefixEnd_476122 244479436180091404185361 := by
  unfold tailWord_476122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341398995274696002219655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11577063987399189339252413 4341398995274696002219655)
  ·
    refine ⟨6512098492912044003329483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341398995274696002219655 6512098492912044003329483)
    ·
      refine ⟨9768147739368066004994225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512098492912044003329483 9768147739368066004994225)
      ·
        refine ⟨7326110804526049503745669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768147739368066004994225 7326110804526049503745669)
        ·
          refine ⟨1373645775848634281952313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7326110804526049503745669 1373645775848634281952313)
          ·
            refine ⟨1030234331886475711464235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373645775848634281952313 1030234331886475711464235)
            ·
              refine ⟨1545351497829713567196353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030234331886475711464235 1545351497829713567196353)
              ·
                refine ⟨1159013623372285175397265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545351497829713567196353 1159013623372285175397265)
                ·
                  refine ⟨869260217529213881547949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159013623372285175397265 869260217529213881547949)
                  ·
                    refine ⟨325972581573455205580481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869260217529213881547949 325972581573455205580481)
                    ·
                      refine ⟨244479436180091404185361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 325972581573455205580481 244479436180091404185361)
                      ·
                        rfl

theorem cell23_476122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_476122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476122 prefixEnd_476122 := by exact prefixLift 476122
  have htrace : WordTrace (prefixWord ++ tailWord_476122) baseStart_476122 baseEnd_476122 := by
    simpa [prefixWord, tailWord_476122, baseEnd_476122] using wordTrace_append hprefix tailTrace_476122
  have hstable : (prefixWord ++ tailWord_476122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476122).length < 2 ^ (prefixWord ++ tailWord_476122).sum := by decide
  have hdescent : baseEnd_476122 < baseStart_476122 := by decide
  rcases family_descends (prefixWord ++ tailWord_476122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476185 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_476185 : Nat := 118140960795 + 476185 * 2 ^ 59
def prefixEnd_476185 : Nat := 4983230072969 + 3 ^ 40 * 476185 * 2
def baseEnd_476185 : Nat := 244511785461324657697571

theorem tailTrace_476185 : CollatzResearch.WordTrace tailWord_476185 prefixEnd_476185 244511785461324657697571 := by
  unfold tailWord_476185
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367893779870545768422009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11578595853247030512281339 17367893779870545768422009)
  ·
    refine ⟨13025920334902909326316507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17367893779870545768422009 13025920334902909326316507)
    ·
      refine ⟨19538880502354363989474761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025920334902909326316507 19538880502354363989474761)
      ·
        refine ⟨14654160376765772992106071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19538880502354363989474761 14654160376765772992106071)
        ·
          refine ⟨21981240565148659488159107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654160376765772992106071 21981240565148659488159107)
          ·
            refine ⟨32971860847722989232238661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21981240565148659488159107 32971860847722989232238661)
            ·
              refine ⟨6182223908948060481044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32971860847722989232238661 6182223908948060481044749)
              ·
                refine ⟨2318333965855522680391781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6182223908948060481044749 2318333965855522680391781)
                ·
                  refine ⟨434687618597910502573459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318333965855522680391781 434687618597910502573459)
                  ·
                    refine ⟨652031427896865753860189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434687618597910502573459 652031427896865753860189)
                    ·
                      refine ⟨244511785461324657697571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652031427896865753860189 244511785461324657697571)
                      ·
                        rfl

theorem cell23_476185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_476185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476185 prefixEnd_476185 := by exact prefixLift 476185
  have htrace : WordTrace (prefixWord ++ tailWord_476185) baseStart_476185 baseEnd_476185 := by
    simpa [prefixWord, tailWord_476185, baseEnd_476185] using wordTrace_append hprefix tailTrace_476185
  have hstable : (prefixWord ++ tailWord_476185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476185).length < 2 ^ (prefixWord ++ tailWord_476185).sum := by decide
  have hdescent : baseEnd_476185 < baseStart_476185 := by decide
  rcases family_descends (prefixWord ++ tailWord_476185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476192 : List Nat := [2, 1, 1, 7, 1, 2, 1, 8]
def baseStart_476192 : Nat := 118140960795 + 476192 * 2 ^ 59
def prefixEnd_476192 : Nat := 4983230072969 + 3 ^ 40 * 476192 * 2
def baseEnd_476192 : Nat := 9056125178737264085557

theorem tailTrace_476192 : CollatzResearch.WordTrace tailWord_476192 prefixEnd_476192 9056125178737264085557 := by
  unfold tailWord_476192
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684074545422592981963415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11578766060563457309284553 8684074545422592981963415)
  ·
    refine ⟨13026111818133889472945123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8684074545422592981963415 13026111818133889472945123)
    ·
      refine ⟨19539167727200834209417685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026111818133889472945123 19539167727200834209417685)
      ·
        refine ⟨457949243606269551783227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19539167727200834209417685 457949243606269551783227)
        ·
          refine ⟨686923865409404327674841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457949243606269551783227 686923865409404327674841)
          ·
            refine ⟨515192899057053245756131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686923865409404327674841 515192899057053245756131)
            ·
              refine ⟨772789348585579868634197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515192899057053245756131 772789348585579868634197)
              ·
                refine ⟨9056125178737264085557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 772789348585579868634197 9056125178737264085557)
                ·
                  rfl

theorem cell23_476192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 8].length) (baseStart_476192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476192 prefixEnd_476192 := by exact prefixLift 476192
  have htrace : WordTrace (prefixWord ++ tailWord_476192) baseStart_476192 baseEnd_476192 := by
    simpa [prefixWord, tailWord_476192, baseEnd_476192] using wordTrace_append hprefix tailTrace_476192
  have hstable : (prefixWord ++ tailWord_476192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476192).length < 2 ^ (prefixWord ++ tailWord_476192).sum := by decide
  have hdescent : baseEnd_476192 < baseStart_476192 := by decide
  rcases family_descends (prefixWord ++ tailWord_476192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476208 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_476208 : Nat := 118140960795 + 476208 * 2 ^ 59
def prefixEnd_476208 : Nat := 4983230072969 + 3 ^ 40 * 476208 * 2
def baseEnd_476208 : Nat := 244523595516378067709965

theorem tailTrace_476208 : CollatzResearch.WordTrace tailWord_476208 prefixEnd_476208 244523595516378067709965 := by
  unfold tailWord_476208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8684366329393610348254639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11579155105858147131006185 8684366329393610348254639)
  ·
    refine ⟨13026549494090415522381959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8684366329393610348254639 13026549494090415522381959)
    ·
      refine ⟨19539824241135623283572939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026549494090415522381959 19539824241135623283572939)
      ·
        refine ⟨29309736361703434925359409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539824241135623283572939 29309736361703434925359409)
        ·
          refine ⟨21982302271277576194019557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29309736361703434925359409 21982302271277576194019557)
          ·
            refine ⟨4121681675864545536378667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21982302271277576194019557 4121681675864545536378667)
            ·
              refine ⟨6182522513796818304568001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121681675864545536378667 6182522513796818304568001)
              ·
                refine ⟨4636891885347613728426001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182522513796818304568001 4636891885347613728426001)
                ·
                  refine ⟨3477668914010710296319501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636891885347613728426001 3477668914010710296319501)
                  ·
                    refine ⟨1304125842754016361119813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477668914010710296319501 1304125842754016361119813)
                    ·
                      refine ⟨244523595516378067709965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1304125842754016361119813 244523595516378067709965)
                      ·
                        rfl

theorem cell23_476208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_476208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476208 prefixEnd_476208 := by exact prefixLift 476208
  have htrace : WordTrace (prefixWord ++ tailWord_476208) baseStart_476208 baseEnd_476208 := by
    simpa [prefixWord, tailWord_476208, baseEnd_476208] using wordTrace_append hprefix tailTrace_476208
  have hstable : (prefixWord ++ tailWord_476208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476208).length < 2 ^ (prefixWord ++ tailWord_476208).sum := by decide
  have hdescent : baseEnd_476208 < baseStart_476208 := by decide
  rcases family_descends (prefixWord ++ tailWord_476208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476229 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_476229 : Nat := 118140960795 + 476229 * 2 ^ 59
def prefixEnd_476229 : Nat := 4983230072969 + 3 ^ 40 * 476229 * 2
def baseEnd_476229 : Nat := 244534378610122485547369

theorem tailTrace_476229 : CollatzResearch.WordTrace tailWord_476229 prefixEnd_476229 244534378610122485547369 := by
  unfold tailWord_476229
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369498591711141283023741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11579665727807427522015827 17369498591711141283023741)
  ·
    refine ⟨6513561971891677981133903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17369498591711141283023741 6513561971891677981133903)
    ·
      refine ⟨9770342957837516971700855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6513561971891677981133903 9770342957837516971700855)
      ·
        refine ⟨14655514436756275457551283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770342957837516971700855 14655514436756275457551283)
        ·
          refine ⟨21983271655134413186326925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655514436756275457551283 21983271655134413186326925)
          ·
            refine ⟨8243726870675404944872597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21983271655134413186326925 8243726870675404944872597)
            ·
              refine ⟨386424697062909606790903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8243726870675404944872597 386424697062909606790903)
              ·
                refine ⟨579637045594364410186355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386424697062909606790903 579637045594364410186355)
                ·
                  refine ⟨869455568391546615279533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579637045594364410186355 869455568391546615279533)
                  ·
                    refine ⟨326045838146829980729825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869455568391546615279533 326045838146829980729825)
                    ·
                      refine ⟨244534378610122485547369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326045838146829980729825 244534378610122485547369)
                      ·
                        rfl

theorem cell23_476229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_476229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476229 prefixEnd_476229 := by exact prefixLift 476229
  have htrace : WordTrace (prefixWord ++ tailWord_476229) baseStart_476229 baseEnd_476229 := by
    simpa [prefixWord, tailWord_476229, baseEnd_476229] using wordTrace_append hprefix tailTrace_476229
  have hstable : (prefixWord ++ tailWord_476229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476229).length < 2 ^ (prefixWord ++ tailWord_476229).sum := by decide
  have hdescent : baseEnd_476229 < baseStart_476229 := by decide
  rcases family_descends (prefixWord ++ tailWord_476229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476253 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_476253 : Nat := 118140960795 + 476253 * 2 ^ 59
def prefixEnd_476253 : Nat := 4983230072969 + 3 ^ 40 * 476253 * 2
def baseEnd_476253 : Nat := 244546702145830391647259

theorem tailTrace_476253 : CollatzResearch.WordTrace tailWord_476253 prefixEnd_476253 244546702145830391647259 := by
  unfold tailWord_476253
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370373943624193381897413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11580249295749462254598275 17370373943624193381897413)
  ·
    refine ⟨3256945114429536259105765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17370373943624193381897413 3256945114429536259105765)
    ·
      refine ⟨610677208955538048582331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3256945114429536259105765 610677208955538048582331)
      ·
        refine ⟨916015813433307072873497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610677208955538048582331 916015813433307072873497)
        ·
          refine ⟨687011860074980304655123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916015813433307072873497 687011860074980304655123)
          ·
            refine ⟨1030517790112470456982685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687011860074980304655123 1030517790112470456982685)
            ·
              refine ⟨386444171292176421368507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1030517790112470456982685 386444171292176421368507)
              ·
                refine ⟨579666256938264632052761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386444171292176421368507 579666256938264632052761)
                ·
                  refine ⟨434749692703698474039571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579666256938264632052761 434749692703698474039571)
                  ·
                    refine ⟨652124539055547711059357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434749692703698474039571 652124539055547711059357)
                    ·
                      refine ⟨244546702145830391647259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652124539055547711059357 244546702145830391647259)
                      ·
                        rfl

theorem cell23_476253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_476253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476253 prefixEnd_476253 := by exact prefixLift 476253
  have htrace : WordTrace (prefixWord ++ tailWord_476253) baseStart_476253 baseEnd_476253 := by
    simpa [prefixWord, tailWord_476253, baseEnd_476253] using wordTrace_append hprefix tailTrace_476253
  have hstable : (prefixWord ++ tailWord_476253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476253).length < 2 ^ (prefixWord ++ tailWord_476253).sum := by decide
  have hdescent : baseEnd_476253 < baseStart_476253 := by decide
  rcases family_descends (prefixWord ++ tailWord_476253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476335 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_476335 : Nat := 118140960795 + 476335 * 2 ^ 59
def prefixEnd_476335 : Nat := 4983230072969 + 3 ^ 40 * 476335 * 2
def baseEnd_476335 : Nat := 244588807559499070821881

theorem tailTrace_476335 : CollatzResearch.WordTrace tailWord_476335 prefixEnd_476335 244588807559499070821881 := by
  unfold tailWord_476335
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373364729327121386382459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11582243152884747590921639 17373364729327121386382459)
  ·
    refine ⟨26060047093990682079573689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17373364729327121386382459 26060047093990682079573689)
    ·
      refine ⟨19545035320493011559680267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26060047093990682079573689 19545035320493011559680267)
      ·
        refine ⟨29317552980739517339520401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19545035320493011559680267 29317552980739517339520401)
        ·
          refine ⟨21988164735554638004640301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29317552980739517339520401 21988164735554638004640301)
          ·
            refine ⟨8245561775832989251740113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21988164735554638004640301 8245561775832989251740113)
            ·
              refine ⟨6184171331874741938805085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245561775832989251740113 6184171331874741938805085)
              ·
                refine ⟨2319064249453028227051907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6184171331874741938805085 2319064249453028227051907)
                ·
                  refine ⟨3478596374179542340577861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319064249453028227051907 3478596374179542340577861)
                  ·
                    refine ⟨652236820158664188858349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478596374179542340577861 652236820158664188858349)
                    ·
                      refine ⟨244588807559499070821881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652236820158664188858349 244588807559499070821881)
                      ·
                        rfl

theorem cell23_476335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_476335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476335 prefixEnd_476335 := by exact prefixLift 476335
  have htrace : WordTrace (prefixWord ++ tailWord_476335) baseStart_476335 baseEnd_476335 := by
    simpa [prefixWord, tailWord_476335, baseEnd_476335] using wordTrace_append hprefix tailTrace_476335
  have hstable : (prefixWord ++ tailWord_476335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476335).length < 2 ^ (prefixWord ++ tailWord_476335).sum := by decide
  have hdescent : baseEnd_476335 < baseStart_476335 := by decide
  rcases family_descends (prefixWord ++ tailWord_476335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476439 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_476439 : Nat := 118140960795 + 476439 * 2 ^ 59
def prefixEnd_476439 : Nat := 4983230072969 + 3 ^ 40 * 476439 * 2
def baseEnd_476439 : Nat := 244642209547566663921403

theorem tailTrace_476439 : CollatzResearch.WordTrace tailWord_476439 prefixEnd_476439 244642209547566663921403 := by
  unfold tailWord_476439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377157920950347148168371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11584771947300231432112247 17377157920950347148168371)
  ·
    refine ⟨26065736881425520722252557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17377157920950347148168371 26065736881425520722252557)
    ·
      refine ⟨9774651330534570270844709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26065736881425520722252557 9774651330534570270844709)
      ·
        refine ⟨1832747124475231925783383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9774651330534570270844709 1832747124475231925783383)
        ·
          refine ⟨2749120686712847888675075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832747124475231925783383 2749120686712847888675075)
          ·
            refine ⟨4123681030069271833012613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749120686712847888675075 4123681030069271833012613)
            ·
              refine ⟨773190193137988468689865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4123681030069271833012613 773190193137988468689865)
              ·
                refine ⟨579892644853491351517399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773190193137988468689865 579892644853491351517399)
                ·
                  refine ⟨869838967280237027276099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579892644853491351517399 869838967280237027276099)
                  ·
                    refine ⟨1304758450920355540914149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869838967280237027276099 1304758450920355540914149)
                    ·
                      refine ⟨244642209547566663921403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1304758450920355540914149 244642209547566663921403)
                      ·
                        rfl

theorem cell23_476439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_476439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476439 prefixEnd_476439 := by exact prefixLift 476439
  have htrace : WordTrace (prefixWord ++ tailWord_476439) baseStart_476439 baseEnd_476439 := by
    simpa [prefixWord, tailWord_476439, baseEnd_476439] using wordTrace_append hprefix tailTrace_476439
  have hstable : (prefixWord ++ tailWord_476439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476439).length < 2 ^ (prefixWord ++ tailWord_476439).sum := by decide
  have hdescent : baseEnd_476439 < baseStart_476439 := by decide
  rcases family_descends (prefixWord ++ tailWord_476439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476450 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_476450 : Nat := 118140960795 + 476450 * 2 ^ 59
def prefixEnd_476450 : Nat := 4983230072969 + 3 ^ 40 * 476450 * 2
def baseEnd_476450 : Nat := 244647857834766120883853

theorem tailTrace_476450 : CollatzResearch.WordTrace tailWord_476450 prefixEnd_476450 244647857834766120883853 := by
  unfold tailWord_476450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344389780977624006704701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11585039415940330684545869 4344389780977624006704701)
  ·
    refine ⟨1629146167866609002514263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4344389780977624006704701 1629146167866609002514263)
    ·
      refine ⟨2443719251799913503771395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629146167866609002514263 2443719251799913503771395)
      ·
        refine ⟨3665578877699870255657093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443719251799913503771395 3665578877699870255657093)
        ·
          refine ⟨687296039568725672935705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3665578877699870255657093 687296039568725672935705)
          ·
            refine ⟨515472029676544254701779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687296039568725672935705 515472029676544254701779)
            ·
              refine ⟨773208044514816382052669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515472029676544254701779 773208044514816382052669)
              ·
                refine ⟨289953016693056143269751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773208044514816382052669 289953016693056143269751)
                ·
                  refine ⟨434929525039584214904627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289953016693056143269751 434929525039584214904627)
                  ·
                    refine ⟨652394287559376322356941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434929525039584214904627 652394287559376322356941)
                    ·
                      refine ⟨244647857834766120883853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652394287559376322356941 244647857834766120883853)
                      ·
                        rfl

theorem cell23_476450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_476450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476450 prefixEnd_476450 := by exact prefixLift 476450
  have htrace : WordTrace (prefixWord ++ tailWord_476450) baseStart_476450 baseEnd_476450 := by
    simpa [prefixWord, tailWord_476450, baseEnd_476450] using wordTrace_append hprefix tailTrace_476450
  have hstable : (prefixWord ++ tailWord_476450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476450).length < 2 ^ (prefixWord ++ tailWord_476450).sum := by decide
  have hdescent : baseEnd_476450 < baseStart_476450 := by decide
  rcases family_descends (prefixWord ++ tailWord_476450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476452 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_476452 : Nat := 118140960795 + 476452 * 2 ^ 59
def prefixEnd_476452 : Nat := 4983230072969 + 3 ^ 40 * 476452 * 2
def baseEnd_476452 : Nat := 244648884796075113058843

theorem tailTrace_476452 : CollatzResearch.WordTrace tailWord_476452 prefixEnd_476452 244648884796075113058843 := by
  unfold tailWord_476452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688816034951625184195805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11585088046602166912261073 8688816034951625184195805)
  ·
    refine ⟨3258306013106859444073427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8688816034951625184195805 3258306013106859444073427)
    ·
      refine ⟨4887459019660289166110141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258306013106859444073427 4887459019660289166110141)
      ·
        refine ⟨1832797132372608437291303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4887459019660289166110141 1832797132372608437291303)
        ·
          refine ⟨2749195698558912655936955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832797132372608437291303 2749195698558912655936955)
          ·
            refine ⟨4123793547838368983905433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749195698558912655936955 4123793547838368983905433)
            ·
              refine ⟨3092845160878776737929075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123793547838368983905433 3092845160878776737929075)
              ·
                refine ⟨4639267741318165106893613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092845160878776737929075 4639267741318165106893613)
                ·
                  refine ⟨1739725402994311915085105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4639267741318165106893613 1739725402994311915085105)
                  ·
                    refine ⟨1304794052245733936313829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739725402994311915085105 1304794052245733936313829)
                    ·
                      refine ⟨244648884796075113058843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1304794052245733936313829 244648884796075113058843)
                      ·
                        rfl

theorem cell23_476452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_476452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476452 prefixEnd_476452 := by exact prefixLift 476452
  have htrace : WordTrace (prefixWord ++ tailWord_476452) baseStart_476452 baseEnd_476452 := by
    simpa [prefixWord, tailWord_476452, baseEnd_476452] using wordTrace_append hprefix tailTrace_476452
  have hstable : (prefixWord ++ tailWord_476452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476452).length < 2 ^ (prefixWord ++ tailWord_476452).sum := by decide
  have hdescent : baseEnd_476452 < baseStart_476452 := by decide
  rcases family_descends (prefixWord ++ tailWord_476452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476493 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_476493 : Nat := 118140960795 + 476493 * 2 ^ 59
def prefixEnd_476493 : Nat := 4983230072969 + 3 ^ 40 * 476493 * 2
def baseEnd_476493 : Nat := 244669937502909452646155

theorem tailTrace_476493 : CollatzResearch.WordTrace tailWord_476493 prefixEnd_476493 244669937502909452646155 := by
  unfold tailWord_476493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379127462754714370634133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586084975169809580422755 17379127462754714370634133)
  ·
    refine ⟨814646599816627236123475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17379127462754714370634133 814646599816627236123475)
    ·
      refine ⟨1221969899724940854185213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814646599816627236123475 1221969899724940854185213)
      ·
        refine ⟨458238712396852820319455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1221969899724940854185213 458238712396852820319455)
        ·
          refine ⟨687358068595279230479183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458238712396852820319455 687358068595279230479183)
          ·
            refine ⟨1031037102892918845718775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687358068595279230479183 1031037102892918845718775)
            ·
              refine ⟨1546555654339378268578163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031037102892918845718775 1546555654339378268578163)
              ·
                refine ⟨2319833481509067402867245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546555654339378268578163 2319833481509067402867245)
                ·
                  refine ⟨869937555565900276075217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319833481509067402867245 869937555565900276075217)
                  ·
                    refine ⟨652453166674425207056413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869937555565900276075217 652453166674425207056413)
                    ·
                      refine ⟨244669937502909452646155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652453166674425207056413 244669937502909452646155)
                      ·
                        rfl

theorem cell23_476493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_476493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476493 prefixEnd_476493 := by exact prefixLift 476493
  have htrace : WordTrace (prefixWord ++ tailWord_476493) baseStart_476493 baseEnd_476493 := by
    simpa [prefixWord, tailWord_476493, baseEnd_476493] using wordTrace_append hprefix tailTrace_476493
  have hstable : (prefixWord ++ tailWord_476493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476493).length < 2 ^ (prefixWord ++ tailWord_476493).sum := by decide
  have hdescent : baseEnd_476493 < baseStart_476493 := by decide
  rcases family_descends (prefixWord ++ tailWord_476493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476499 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 3, 3, 2]
def baseStart_476499 : Nat := 118140960795 + 476499 * 2 ^ 59
def prefixEnd_476499 : Nat := 4983230072969 + 3 ^ 40 * 476499 * 2
def baseEnd_476499 : Nat := 244673018386836429171127

theorem tailTrace_476499 : CollatzResearch.WordTrace tailWord_476499 prefixEnd_476499 244673018386836429171127 := by
  unfold tailWord_476499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379346300732977395352551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11586230867155318263568367 17379346300732977395352551)
  ·
    refine ⟨26069019451099466093028827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17379346300732977395352551 26069019451099466093028827)
    ·
      refine ⟨39103529176649199139543241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26069019451099466093028827 39103529176649199139543241)
      ·
        refine ⟨29327646882486899354657431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39103529176649199139543241 29327646882486899354657431)
        ·
          refine ⟨43991470323730349031986147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29327646882486899354657431 43991470323730349031986147)
          ·
            refine ⟨65987205485595523547979221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43991470323730349031986147 65987205485595523547979221)
            ·
              refine ⟨1546575128568645083155763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65987205485595523547979221 1546575128568645083155763)
              ·
                refine ⟨2319862692852967624733645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546575128568645083155763 2319862692852967624733645)
                ·
                  refine ⟨869948509819862859275117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319862692852967624733645 869948509819862859275117)
                  ·
                    refine ⟨326230691182448572228169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869948509819862859275117 326230691182448572228169)
                    ·
                      refine ⟨244673018386836429171127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326230691182448572228169 244673018386836429171127)
                      ·
                        rfl

theorem cell23_476499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3, 2].length) (baseStart_476499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476499 prefixEnd_476499 := by exact prefixLift 476499
  have htrace : WordTrace (prefixWord ++ tailWord_476499) baseStart_476499 baseEnd_476499 := by
    simpa [prefixWord, tailWord_476499, baseEnd_476499] using wordTrace_append hprefix tailTrace_476499
  have hstable : (prefixWord ++ tailWord_476499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476499).length < 2 ^ (prefixWord ++ tailWord_476499).sum := by decide
  have hdescent : baseEnd_476499 < baseStart_476499 := by decide
  rcases family_descends (prefixWord ++ tailWord_476499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476552 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 9]
def baseStart_476552 : Nat := 118140960795 + 476552 * 2 ^ 59
def prefixEnd_476552 : Nat := 4983230072969 + 3 ^ 40 * 476552 * 2
def baseEnd_476552 : Nat := 27188914762391635756487

theorem tailTrace_476552 : CollatzResearch.WordTrace tailWord_476552 prefixEnd_476552 27188914762391635756487 := by
  unfold tailWord_476552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690639684770483723515955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11587519579693978298021273 8690639684770483723515955)
  ·
    refine ⟨13035959527155725585273933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690639684770483723515955 13035959527155725585273933)
    ·
      refine ⟨4888484822683397094477725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13035959527155725585273933 4888484822683397094477725)
      ·
        refine ⟨1833181808506273910429147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4888484822683397094477725 1833181808506273910429147)
        ·
          refine ⟨2749772712759410865643721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833181808506273910429147 2749772712759410865643721)
          ·
            refine ⟨2062329534569558149232791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749772712759410865643721 2062329534569558149232791)
            ·
              refine ⟨3093494301854337223849187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062329534569558149232791 3093494301854337223849187)
              ·
                refine ⟨4640241452781505835773781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093494301854337223849187 4640241452781505835773781)
                ·
                  refine ⟨27188914762391635756487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4640241452781505835773781 27188914762391635756487)
                  ·
                    rfl

theorem cell23_476552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_476552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476552 prefixEnd_476552 := by exact prefixLift 476552
  have htrace : WordTrace (prefixWord ++ tailWord_476552) baseStart_476552 baseEnd_476552 := by
    simpa [prefixWord, tailWord_476552, baseEnd_476552] using wordTrace_append hprefix tailTrace_476552
  have hstable : (prefixWord ++ tailWord_476552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476552).length < 2 ^ (prefixWord ++ tailWord_476552).sum := by decide
  have hdescent : baseEnd_476552 < baseStart_476552 := by decide
  rcases family_descends (prefixWord ++ tailWord_476552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476569 : List Nat := [1, 2, 1, 2, 1, 5, 1, 5, 5]
def baseStart_476569 : Nat := 118140960795 + 476569 * 2 ^ 59
def prefixEnd_476569 : Nat := 4983230072969 + 3 ^ 40 * 476569 * 2
def baseEnd_476569 : Nat := 27189884670294572810645

theorem tailTrace_476569 : CollatzResearch.WordTrace tailWord_476569 prefixEnd_476569 27189884670294572810645 := by
  unfold tailWord_476569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381899410479379350400761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11587932940319586233600507 17381899410479379350400761)
  ·
    refine ⟨13036424557859534512800571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17381899410479379350400761 13036424557859534512800571)
    ·
      refine ⟨19554636836789301769200857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036424557859534512800571 19554636836789301769200857)
      ·
        refine ⟨14665977627591976326900643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19554636836789301769200857 14665977627591976326900643)
        ·
          refine ⟨21998966441387964490350965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665977627591976326900643 21998966441387964490350965)
          ·
            refine ⟨2062403103880121670970403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21998966441387964490350965 2062403103880121670970403)
            ·
              refine ⟨3093604655820182506455605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062403103880121670970403 3093604655820182506455605)
              ·
                refine ⟨290025436483142109980213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3093604655820182506455605 290025436483142109980213)
                ·
                  refine ⟨27189884670294572810645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290025436483142109980213 27189884670294572810645)
                  ·
                    rfl

theorem cell23_476569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 5, 5].length) (baseStart_476569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476569 prefixEnd_476569 := by exact prefixLift 476569
  have htrace : WordTrace (prefixWord ++ tailWord_476569) baseStart_476569 baseEnd_476569 := by
    simpa [prefixWord, tailWord_476569, baseEnd_476569] using wordTrace_append hprefix tailTrace_476569
  have hstable : (prefixWord ++ tailWord_476569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476569).length < 2 ^ (prefixWord ++ tailWord_476569).sum := by decide
  have hdescent : baseEnd_476569 < baseStart_476569 := by decide
  rcases family_descends (prefixWord ++ tailWord_476569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476619 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 6, 2]
def baseStart_476619 : Nat := 118140960795 + 476619 * 2 ^ 59
def prefixEnd_476619 : Nat := 4983230072969 + 3 ^ 40 * 476619 * 2
def baseEnd_476619 : Nat := 244734636065375959670575

theorem tailTrace_476619 : CollatzResearch.WordTrace tailWord_476619 prefixEnd_476619 244734636065375959670575 := by
  unfold tailWord_476619
  simp only [CollatzResearch.WordTrace]
  refine ⟨17383723060298237889720911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11589148706865491926480607 17383723060298237889720911)
  ·
    refine ⟨26075584590447356834581367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17383723060298237889720911 26075584590447356834581367)
    ·
      refine ⟨39113376885671035251872051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26075584590447356834581367 39113376885671035251872051)
      ·
        refine ⟨58670065328506552877808077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39113376885671035251872051 58670065328506552877808077)
        ·
          refine ⟨22001274498189957329178029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58670065328506552877808077 22001274498189957329178029)
          ·
            refine ⟨8250477936821233998441761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22001274498189957329178029 8250477936821233998441761)
            ·
              refine ⟨6187858452615925498831321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8250477936821233998441761 6187858452615925498831321)
              ·
                refine ⟨4640893839461944124123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187858452615925498831321 4640893839461944124123491)
                ·
                  refine ⟨6961340759192916186185237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640893839461944124123491 6961340759192916186185237)
                  ·
                    refine ⟨326312848087167946227433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6961340759192916186185237 326312848087167946227433)
                    ·
                      refine ⟨244734636065375959670575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326312848087167946227433 244734636065375959670575)
                      ·
                        rfl

theorem cell23_476619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6, 2].length) (baseStart_476619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476619 prefixEnd_476619 := by exact prefixLift 476619
  have htrace : WordTrace (prefixWord ++ tailWord_476619) baseStart_476619 baseEnd_476619 := by
    simpa [prefixWord, tailWord_476619, baseEnd_476619] using wordTrace_append hprefix tailTrace_476619
  have hstable : (prefixWord ++ tailWord_476619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476619).length < 2 ^ (prefixWord ++ tailWord_476619).sum := by decide
  have hdescent : baseEnd_476619 < baseStart_476619 := by decide
  rcases family_descends (prefixWord ++ tailWord_476619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476632 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_476632 : Nat := 118140960795 + 476632 * 2 ^ 59
def prefixEnd_476632 : Nat := 4983230072969 + 3 ^ 40 * 476632 * 2
def baseEnd_476632 : Nat := 244741311313884408808015

theorem tailTrace_476632 : CollatzResearch.WordTrace tailWord_476632 prefixEnd_476632 244741311313884408808015 := by
  unfold tailWord_476632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692098604625570554972075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11589464806167427406629433 8692098604625570554972075)
  ·
    refine ⟨13038147906938355832458113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8692098604625570554972075 13038147906938355832458113)
    ·
      refine ⟨9778610930203766874343585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13038147906938355832458113 9778610930203766874343585)
      ·
        refine ⟨7333958197652825155757689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9778610930203766874343585 7333958197652825155757689)
        ·
          refine ⟨5500468648239618866818267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7333958197652825155757689 5500468648239618866818267)
          ·
            refine ⟨8250702972359428300227401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500468648239618866818267 8250702972359428300227401)
            ·
              refine ⟨6188027229269571225170551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8250702972359428300227401 6188027229269571225170551)
              ·
                refine ⟨9282040843904356837755827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6188027229269571225170551 9282040843904356837755827)
                ·
                  refine ⟨13923061265856535256633741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282040843904356837755827 13923061265856535256633741)
                  ·
                    refine ⟨5221147974696200721237653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13923061265856535256633741 5221147974696200721237653)
                    ·
                      refine ⟨244741311313884408808015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5221147974696200721237653 244741311313884408808015)
                      ·
                        rfl

theorem cell23_476632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_476632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476632 prefixEnd_476632 := by exact prefixLift 476632
  have htrace : WordTrace (prefixWord ++ tailWord_476632) baseStart_476632 baseEnd_476632 := by
    simpa [prefixWord, tailWord_476632, baseEnd_476632] using wordTrace_append hprefix tailTrace_476632
  have hstable : (prefixWord ++ tailWord_476632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476632).length < 2 ^ (prefixWord ++ tailWord_476632).sum := by decide
  have hdescent : baseEnd_476632 < baseStart_476632 := by decide
  rcases family_descends (prefixWord ++ tailWord_476632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476670 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_476670 : Nat := 118140960795 + 476670 * 2 ^ 59
def prefixEnd_476670 : Nat := 4983230072969 + 3 ^ 40 * 476670 * 2
def baseEnd_476670 : Nat := 244760823578755260132841

theorem tailTrace_476670 : CollatzResearch.WordTrace tailWord_476670 prefixEnd_476670 244760823578755260132841 := by
  unfold tailWord_476670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173197897889184199978433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11590388788742315733218309 2173197897889184199978433)
  ·
    refine ⟨1629898423416888149983825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2173197897889184199978433 1629898423416888149983825)
    ·
      refine ⟨1222423817562666112487869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1629898423416888149983825 1222423817562666112487869)
      ·
        refine ⟨458408931585999792182951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1222423817562666112487869 458408931585999792182951)
        ·
          refine ⟨687613397378999688274427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458408931585999792182951 687613397378999688274427)
          ·
            refine ⟨1031420096068499532411641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687613397378999688274427 1031420096068499532411641)
            ·
              refine ⟨773565072051374649308731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031420096068499532411641 773565072051374649308731)
              ·
                refine ⟨1160347608077061973963097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773565072051374649308731 1160347608077061973963097)
                ·
                  refine ⟨870260706057796480472323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160347608077061973963097 870260706057796480472323)
                  ·
                    refine ⟨1305391059086694720708485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 870260706057796480472323 1305391059086694720708485)
                    ·
                      refine ⟨244760823578755260132841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1305391059086694720708485 244760823578755260132841)
                      ·
                        rfl

theorem cell23_476670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_476670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476670 prefixEnd_476670 := by exact prefixLift 476670
  have htrace : WordTrace (prefixWord ++ tailWord_476670) baseStart_476670 baseEnd_476670 := by
    simpa [prefixWord, tailWord_476670, baseEnd_476670] using wordTrace_append hprefix tailTrace_476670
  have hstable : (prefixWord ++ tailWord_476670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476670).length < 2 ^ (prefixWord ++ tailWord_476670).sum := by decide
  have hdescent : baseEnd_476670 < baseStart_476670 := by decide
  rcases family_descends (prefixWord ++ tailWord_476670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476673 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_476673 : Nat := 118140960795 + 476673 * 2 ^ 59
def prefixEnd_476673 : Nat := 4983230072969 + 3 ^ 40 * 476673 * 2
def baseEnd_476673 : Nat := 244762364020718748395327

theorem tailTrace_476673 : CollatzResearch.WordTrace tailWord_476673 prefixEnd_476673 244762364020718748395327 := by
  unfold tailWord_476673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385692602102605112186673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11590461734735070074791115 17385692602102605112186673)
  ·
    refine ⟨13039269451576953834140005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17385692602102605112186673 13039269451576953834140005)
    ·
      refine ⟨2444863022170678843901251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13039269451576953834140005 2444863022170678843901251)
      ·
        refine ⟨3667294533256018265851877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444863022170678843901251 3667294533256018265851877)
        ·
          refine ⟨687617724985503424847227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3667294533256018265851877 687617724985503424847227)
          ·
            refine ⟨1031426587478255137270841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687617724985503424847227 1031426587478255137270841)
            ·
              refine ⟨773569940608691352953131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031426587478255137270841 773569940608691352953131)
              ·
                refine ⟨1160354910913037029429697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773569940608691352953131 1160354910913037029429697)
                ·
                  refine ⟨870266183184777772072273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160354910913037029429697 870266183184777772072273)
                  ·
                    refine ⟨652699637388583329054205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 870266183184777772072273 652699637388583329054205)
                    ·
                      refine ⟨244762364020718748395327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 652699637388583329054205 244762364020718748395327)
                      ·
                        rfl

theorem cell23_476673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_476673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476673 prefixEnd_476673 := by exact prefixLift 476673
  have htrace : WordTrace (prefixWord ++ tailWord_476673) baseStart_476673 baseEnd_476673 := by
    simpa [prefixWord, tailWord_476673, baseEnd_476673] using wordTrace_append hprefix tailTrace_476673
  have hstable : (prefixWord ++ tailWord_476673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476673).length < 2 ^ (prefixWord ++ tailWord_476673).sum := by decide
  have hdescent : baseEnd_476673 < baseStart_476673 := by decide
  rcases family_descends (prefixWord ++ tailWord_476673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476743 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_476743 : Nat := 118140960795 + 476743 * 2 ^ 59
def prefixEnd_476743 : Nat := 4983230072969 + 3 ^ 40 * 476743 * 2
def baseEnd_476743 : Nat := 244798307666533474520005

theorem tailTrace_476743 : CollatzResearch.WordTrace tailWord_476743 prefixEnd_476743 244798307666533474520005 := by
  unfold tailWord_476743
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388245711849007067234883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11592163807899338044823255 17388245711849007067234883)
  ·
    refine ⟨26082368567773510600852325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17388245711849007067234883 26082368567773510600852325)
    ·
      refine ⟨4890444106457533237659811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26082368567773510600852325 4890444106457533237659811)
      ·
        refine ⟨7335666159686299856489717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890444106457533237659811 7335666159686299856489717)
        ·
          refine ⟨687718702470590611545911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7335666159686299856489717 687718702470590611545911)
          ·
            refine ⟨1031578053705885917318867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687718702470590611545911 1031578053705885917318867)
            ·
              refine ⟨1547367080558828875978301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031578053705885917318867 1547367080558828875978301)
              ·
                refine ⟨580262655209560828491863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1547367080558828875978301 580262655209560828491863)
                ·
                  refine ⟨870393982814341242737795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580262655209560828491863 870393982814341242737795)
                  ·
                    refine ⟨1305590974221511864106693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 870393982814341242737795 1305590974221511864106693)
                    ·
                      refine ⟨244798307666533474520005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1305590974221511864106693 244798307666533474520005)
                      ·
                        rfl

theorem cell23_476743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_476743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476743 prefixEnd_476743 := by exact prefixLift 476743
  have htrace : WordTrace (prefixWord ++ tailWord_476743) baseStart_476743 baseEnd_476743 := by
    simpa [prefixWord, tailWord_476743, baseEnd_476743] using wordTrace_append hprefix tailTrace_476743
  have hstable : (prefixWord ++ tailWord_476743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476743).length < 2 ^ (prefixWord ++ tailWord_476743).sum := by decide
  have hdescent : baseEnd_476743 < baseStart_476743 := by decide
  rcases family_descends (prefixWord ++ tailWord_476743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476773 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_476773 : Nat := 118140960795 + 476773 * 2 ^ 59
def prefixEnd_476773 : Nat := 4983230072969 + 3 ^ 40 * 476773 * 2
def baseEnd_476773 : Nat := 244813712086168357144867

theorem tailTrace_476773 : CollatzResearch.WordTrace tailWord_476773 prefixEnd_476773 244813712086168357144867 := by
  unfold tailWord_476773
  simp only [CollatzResearch.WordTrace]
  refine ⟨17389339901740322190826973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11592893267826881460551315 17389339901740322190826973)
  ·
    refine ⟨6521002463152620821560115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17389339901740322190826973 6521002463152620821560115)
    ·
      refine ⟨9781503694728931232340173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6521002463152620821560115 9781503694728931232340173)
      ·
        refine ⟨3668063885523349212127565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9781503694728931232340173 3668063885523349212127565)
        ·
          refine ⟨1375523957071255954547837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3668063885523349212127565 1375523957071255954547837)
          ·
            refine ⟨515821483901720982955439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1375523957071255954547837 515821483901720982955439)
            ·
              refine ⟨773732225852581474433159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515821483901720982955439 773732225852581474433159)
              ·
                refine ⟨1160598338778872211649739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773732225852581474433159 1160598338778872211649739)
                ·
                  refine ⟨1740897508168308317474609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160598338778872211649739 1740897508168308317474609)
                  ·
                    refine ⟨1305673131126231238105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740897508168308317474609 1305673131126231238105957)
                    ·
                      refine ⟨244813712086168357144867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1305673131126231238105957 244813712086168357144867)
                      ·
                        rfl

theorem cell23_476773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_476773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476773 prefixEnd_476773 := by exact prefixLift 476773
  have htrace : WordTrace (prefixWord ++ tailWord_476773) baseStart_476773 baseEnd_476773 := by
    simpa [prefixWord, tailWord_476773, baseEnd_476773] using wordTrace_append hprefix tailTrace_476773
  have hstable : (prefixWord ++ tailWord_476773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476773).length < 2 ^ (prefixWord ++ tailWord_476773).sum := by decide
  have hdescent : baseEnd_476773 < baseStart_476773 := by decide
  rcases family_descends (prefixWord ++ tailWord_476773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476809 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_476809 : Nat := 118140960795 + 476809 * 2 ^ 59
def prefixEnd_476809 : Nat := 4983230072969 + 3 ^ 40 * 476809 * 2
def baseEnd_476809 : Nat := 81610732463243405431567

theorem tailTrace_476809 : CollatzResearch.WordTrace tailWord_476809 prefixEnd_476809 81610732463243405431567 := by
  unfold tailWord_476809
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390652929609900339137481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11593768619739933559424987 17390652929609900339137481)
  ·
    refine ⟨13042989697207425254353111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17390652929609900339137481 13042989697207425254353111)
    ·
      refine ⟨19564484545811137881529667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042989697207425254353111 19564484545811137881529667)
      ·
        refine ⟨29346726818716706822294501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564484545811137881529667 29346726818716706822294501)
        ·
          refine ⟨5502511278509382529180219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29346726818716706822294501 5502511278509382529180219)
          ·
            refine ⟨8253766917764073793770329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502511278509382529180219 8253766917764073793770329)
            ·
              refine ⟨6190325188323055345327747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8253766917764073793770329 6190325188323055345327747)
              ·
                refine ⟨9285487782484583017991621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190325188323055345327747 9285487782484583017991621)
                ·
                  refine ⟨1741028959215859315873429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9285487782484583017991621 1741028959215859315873429)
                  ·
                    refine ⟨81610732463243405431567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1741028959215859315873429 81610732463243405431567)
                    ·
                      rfl

theorem cell23_476809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_476809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476809 prefixEnd_476809 := by exact prefixLift 476809
  have htrace : WordTrace (prefixWord ++ tailWord_476809) baseStart_476809 baseEnd_476809 := by
    simpa [prefixWord, tailWord_476809, baseEnd_476809] using wordTrace_append hprefix tailTrace_476809
  have hstable : (prefixWord ++ tailWord_476809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476809).length < 2 ^ (prefixWord ++ tailWord_476809).sum := by decide
  have hdescent : baseEnd_476809 < baseStart_476809 := by decide
  rcases family_descends (prefixWord ++ tailWord_476809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476819 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5]
def baseStart_476819 : Nat := 118140960795 + 476819 * 2 ^ 59
def prefixEnd_476819 : Nat := 4983230072969 + 3 ^ 40 * 476819 * 2
def baseEnd_476819 : Nat := 244837332196275177169655

theorem tailTrace_476819 : CollatzResearch.WordTrace tailWord_476819 prefixEnd_476819 244837332196275177169655 := by
  unfold tailWord_476819
  simp only [CollatzResearch.WordTrace]
  refine ⟨17391017659573672047001511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11594011773049114698001007 17391017659573672047001511)
  ·
    refine ⟨26086526489360508070502267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17391017659573672047001511 26086526489360508070502267)
    ·
      refine ⟨39129789734040762105753401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26086526489360508070502267 39129789734040762105753401)
      ·
        refine ⟨29347342300530571579315051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39129789734040762105753401 29347342300530571579315051)
        ·
          refine ⟨44021013450795857368972577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29347342300530571579315051 44021013450795857368972577)
          ·
            refine ⟨33015760088096893026729433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44021013450795857368972577 33015760088096893026729433)
            ·
              refine ⟨24761820066072669770047075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33015760088096893026729433 24761820066072669770047075)
              ·
                refine ⟨37142730099109004655070613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24761820066072669770047075 37142730099109004655070613)
                ·
                  refine ⟨1741065473395734593206435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37142730099109004655070613 1741065473395734593206435)
                  ·
                    refine ⟨2611598210093601889809653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741065473395734593206435 2611598210093601889809653)
                    ·
                      refine ⟨244837332196275177169655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2611598210093601889809653 244837332196275177169655)
                      ·
                        rfl

theorem cell23_476819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_476819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476819 prefixEnd_476819 := by exact prefixLift 476819
  have htrace : WordTrace (prefixWord ++ tailWord_476819) baseStart_476819 baseEnd_476819 := by
    simpa [prefixWord, tailWord_476819, baseEnd_476819] using wordTrace_append hprefix tailTrace_476819
  have hstable : (prefixWord ++ tailWord_476819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476819).length < 2 ^ (prefixWord ++ tailWord_476819).sum := by decide
  have hdescent : baseEnd_476819 < baseStart_476819 := by decide
  rcases family_descends (prefixWord ++ tailWord_476819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476836 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_476836 : Nat := 118140960795 + 476836 * 2 ^ 59
def prefixEnd_476836 : Nat := 4983230072969 + 3 ^ 40 * 476836 * 2
def baseEnd_476836 : Nat := 244846061367401610657077

theorem tailTrace_476836 : CollatzResearch.WordTrace tailWord_476836 prefixEnd_476836 244846061367401610657077 := by
  unfold tailWord_476836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695818850256041975185181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11594425133674722633580241 8695818850256041975185181)
  ·
    refine ⟨3260932068846015740694443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8695818850256041975185181 3260932068846015740694443)
    ·
      refine ⟨4891398103269023611041665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260932068846015740694443 4891398103269023611041665)
      ·
        refine ⟨3668548577451767708281249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891398103269023611041665 3668548577451767708281249)
        ·
          refine ⟨2751411433088825781210937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3668548577451767708281249 2751411433088825781210937)
          ·
            refine ⟨2063558574816619335908203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751411433088825781210937 2063558574816619335908203)
            ·
              refine ⟨3095337862224929003862305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063558574816619335908203 3095337862224929003862305)
              ·
                refine ⟨2321503396668696752896729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095337862224929003862305 2321503396668696752896729)
                ·
                  refine ⟨1741127547501522564672547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321503396668696752896729 1741127547501522564672547)
                  ·
                    refine ⟨2611691321252283847008821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741127547501522564672547 2611691321252283847008821)
                    ·
                      refine ⟨244846061367401610657077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2611691321252283847008821 244846061367401610657077)
                      ·
                        rfl

theorem cell23_476836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_476836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476836 prefixEnd_476836 := by exact prefixLift 476836
  have htrace : WordTrace (prefixWord ++ tailWord_476836) baseStart_476836 baseEnd_476836 := by
    simpa [prefixWord, tailWord_476836, baseEnd_476836] using wordTrace_append hprefix tailTrace_476836
  have hstable : (prefixWord ++ tailWord_476836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476836).length < 2 ^ (prefixWord ++ tailWord_476836).sum := by decide
  have hdescent : baseEnd_476836 < baseStart_476836 := by decide
  rcases family_descends (prefixWord ++ tailWord_476836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476936 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_476936 : Nat := 118140960795 + 476936 * 2 ^ 59
def prefixEnd_476936 : Nat := 4983230072969 + 3 ^ 40 * 476936 * 2
def baseEnd_476936 : Nat := 244897409432851219406617

theorem tailTrace_476936 : CollatzResearch.WordTrace tailWord_476936 prefixEnd_476936 244897409432851219406617 := by
  unfold tailWord_476936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697642500074900514505331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11596856666766534019340441 8697642500074900514505331)
  ·
    refine ⟨13046463750112350771757997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8697642500074900514505331 13046463750112350771757997)
    ·
      refine ⟨4892423906292131539409249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13046463750112350771757997 4892423906292131539409249)
      ·
        refine ⟨3669317929719098654556937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4892423906292131539409249 3669317929719098654556937)
        ·
          refine ⟨2751988447289323990917703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669317929719098654556937 2751988447289323990917703)
          ·
            refine ⟨4127982670933985986376555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751988447289323990917703 4127982670933985986376555)
            ·
              refine ⟨6191974006400978979564833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127982670933985986376555 6191974006400978979564833)
              ·
                refine ⟨4643980504800734234673625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191974006400978979564833 4643980504800734234673625)
                ·
                  refine ⟨3482985378600550676005219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643980504800734234673625 3482985378600550676005219)
                  ·
                    refine ⟨5224478067900826014007829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482985378600550676005219 5224478067900826014007829)
                    ·
                      refine ⟨244897409432851219406617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5224478067900826014007829 244897409432851219406617)
                      ·
                        rfl

theorem cell23_476936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_476936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476936 prefixEnd_476936 := by exact prefixLift 476936
  have htrace : WordTrace (prefixWord ++ tailWord_476936) baseStart_476936 baseEnd_476936 := by
    simpa [prefixWord, tailWord_476936, baseEnd_476936] using wordTrace_append hprefix tailTrace_476936
  have hstable : (prefixWord ++ tailWord_476936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476936).length < 2 ^ (prefixWord ++ tailWord_476936).sum := by decide
  have hdescent : baseEnd_476936 < baseStart_476936 := by decide
  rcases family_descends (prefixWord ++ tailWord_476936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476976 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_476976 : Nat := 118140960795 + 476976 * 2 ^ 59
def prefixEnd_476976 : Nat := 4983230072969 + 3 ^ 40 * 476976 * 2
def baseEnd_476976 : Nat := 81639316219677020968811

theorem tailTrace_476976 : CollatzResearch.WordTrace tailWord_476976 prefixEnd_476976 81639316219677020968811 := by
  unfold tailWord_476976
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698371960002443930233391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11597829280003258573644521 8698371960002443930233391)
  ·
    refine ⟨13047557940003665895350087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8698371960002443930233391 13047557940003665895350087)
    ·
      refine ⟨19571336910005498843025131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13047557940003665895350087 19571336910005498843025131)
      ·
        refine ⟨29357005365008248264537697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19571336910005498843025131 29357005365008248264537697)
        ·
          refine ⟨22017754023756186198403273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29357005365008248264537697 22017754023756186198403273)
          ·
            refine ⟨16513315517817139648802455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22017754023756186198403273 16513315517817139648802455)
            ·
              refine ⟨24769973276725709473203683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16513315517817139648802455 24769973276725709473203683)
              ·
                refine ⟨37154959915088564209805525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24769973276725709473203683 37154959915088564209805525)
                ·
                  refine ⟨870819373009888223667317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37154959915088564209805525 870819373009888223667317)
                  ·
                    refine ⟨81639316219677020968811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 870819373009888223667317 81639316219677020968811)
                    ·
                      rfl

theorem cell23_476976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_476976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476976 prefixEnd_476976 := by exact prefixLift 476976
  have htrace : WordTrace (prefixWord ++ tailWord_476976) baseStart_476976 baseEnd_476976 := by
    simpa [prefixWord, tailWord_476976, baseEnd_476976] using wordTrace_append hprefix tailTrace_476976
  have hstable : (prefixWord ++ tailWord_476976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476976).length < 2 ^ (prefixWord ++ tailWord_476976).sum := by decide
  have hdescent : baseEnd_476976 < baseStart_476976 := by decide
  rcases family_descends (prefixWord ++ tailWord_476976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_476983 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_476983 : Nat := 118140960795 + 476983 * 2 ^ 59
def prefixEnd_476983 : Nat := 4983230072969 + 3 ^ 40 * 476983 * 2
def baseEnd_476983 : Nat := 244921543023612535518901

theorem tailTrace_476983 : CollatzResearch.WordTrace tailWord_476983 prefixEnd_476983 244921543023612535518901 := by
  unfold tailWord_476983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396999230979528055971603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11597999487319685370647735 17396999230979528055971603)
  ·
    refine ⟨26095498846469292083957405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396999230979528055971603 26095498846469292083957405)
    ·
      refine ⟨9785812067425984531484027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26095498846469292083957405 9785812067425984531484027)
      ·
        refine ⟨14678718101138976797226041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785812067425984531484027 14678718101138976797226041)
        ·
          refine ⟨11009038575854232597919531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14678718101138976797226041 11009038575854232597919531)
          ·
            refine ⟨16513557863781348896879297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009038575854232597919531 16513557863781348896879297)
            ·
              refine ⟨12385168397836011672659473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16513557863781348896879297 12385168397836011672659473)
              ·
                refine ⟨9288876298377008754494605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12385168397836011672659473 9288876298377008754494605)
                ·
                  refine ⟨3483328611891378282935477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9288876298377008754494605 3483328611891378282935477)
                  ·
                    refine ⟨326562057364816714025201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3483328611891378282935477 326562057364816714025201)
                    ·
                      refine ⟨244921543023612535518901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326562057364816714025201 244921543023612535518901)
                      ·
                        rfl

theorem cell23_476983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_476983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_476983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_476983 prefixEnd_476983 := by exact prefixLift 476983
  have htrace : WordTrace (prefixWord ++ tailWord_476983) baseStart_476983 baseEnd_476983 := by
    simpa [prefixWord, tailWord_476983, baseEnd_476983] using wordTrace_append hprefix tailTrace_476983
  have hstable : (prefixWord ++ tailWord_476983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_476983).length < 2 ^ (prefixWord ++ tailWord_476983).sum := by decide
  have hdescent : baseEnd_476983 < baseStart_476983 := by decide
  rcases family_descends (prefixWord ++ tailWord_476983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477010 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_477010 : Nat := 118140960795 + 477010 * 2 ^ 59
def prefixEnd_477010 : Nat := 4983230072969 + 3 ^ 40 * 477010 * 2
def baseEnd_477010 : Nat := 81645135667094643293759

theorem tailTrace_477010 : CollatzResearch.WordTrace tailWord_477010 prefixEnd_477010 81645135667094643293759 := by
  unfold tailWord_477010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349496000470427916801121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11598656001254474444802989 4349496000470427916801121)
  ·
    refine ⟨3262122000352820937600841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4349496000470427916801121 3262122000352820937600841)
    ·
      refine ⟨2446591500264615703200631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3262122000352820937600841 2446591500264615703200631)
      ·
        refine ⟨3669887250396923554800947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446591500264615703200631 3669887250396923554800947)
        ·
          refine ⟨5504830875595385332201421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669887250396923554800947 5504830875595385332201421)
          ·
            refine ⟨2064311578348269499575533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5504830875595385332201421 2064311578348269499575533)
            ·
              refine ⟨774116841880601062340825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2064311578348269499575533 774116841880601062340825)
              ·
                refine ⟨580587631410450796755619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774116841880601062340825 580587631410450796755619)
                ·
                  refine ⟨870881447115676195133429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580587631410450796755619 870881447115676195133429)
                  ·
                    refine ⟨81645135667094643293759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 870881447115676195133429 81645135667094643293759)
                    ·
                      rfl

theorem cell23_477010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_477010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477010 prefixEnd_477010 := by exact prefixLift 477010
  have htrace : WordTrace (prefixWord ++ tailWord_477010) baseStart_477010 baseEnd_477010 := by
    simpa [prefixWord, tailWord_477010, baseEnd_477010] using wordTrace_append hprefix tailTrace_477010
  have hstable : (prefixWord ++ tailWord_477010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477010).length < 2 ^ (prefixWord ++ tailWord_477010).sum := by decide
  have hdescent : baseEnd_477010 < baseStart_477010 := by decide
  rcases family_descends (prefixWord ++ tailWord_477010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477016 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_477016 : Nat := 118140960795 + 477016 * 2 ^ 59
def prefixEnd_477016 : Nat := 4983230072969 + 3 ^ 40 * 477016 * 2
def baseEnd_477016 : Nat := 244938487885210906406249

theorem tailTrace_477016 : CollatzResearch.WordTrace tailWord_477016 prefixEnd_477016 244938487885210906406249 := by
  unfold tailWord_477016
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699101419929987345961451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11598801893239983127948601 8699101419929987345961451)
  ·
    refine ⟨13048652129894981018942177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8699101419929987345961451 13048652129894981018942177)
    ·
      refine ⟨9786489097421235764206633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13048652129894981018942177 9786489097421235764206633)
      ·
        refine ⟨7339866823065926823154975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9786489097421235764206633 7339866823065926823154975)
        ·
          refine ⟨11009800234598890234732463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339866823065926823154975 11009800234598890234732463)
          ·
            refine ⟨16514700351898335352098695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009800234598890234732463 16514700351898335352098695)
            ·
              refine ⟨24772050527847503028148043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16514700351898335352098695 24772050527847503028148043)
              ·
                refine ⟨37158075791771254542222065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24772050527847503028148043 37158075791771254542222065)
                ·
                  refine ⟨27868556843828440906666549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37158075791771254542222065 27868556843828440906666549)
                  ·
                    refine ⟨2612677204108916334999989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27868556843828440906666549 2612677204108916334999989)
                    ·
                      refine ⟨244938487885210906406249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2612677204108916334999989 244938487885210906406249)
                      ·
                        rfl

theorem cell23_477016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_477016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477016 prefixEnd_477016 := by exact prefixLift 477016
  have htrace : WordTrace (prefixWord ++ tailWord_477016) baseStart_477016 baseEnd_477016 := by
    simpa [prefixWord, tailWord_477016, baseEnd_477016] using wordTrace_append hprefix tailTrace_477016
  have hstable : (prefixWord ++ tailWord_477016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477016).length < 2 ^ (prefixWord ++ tailWord_477016).sum := by decide
  have hdescent : baseEnd_477016 < baseStart_477016 := by decide
  rcases family_descends (prefixWord ++ tailWord_477016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477023 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 1, 6]
def baseStart_477023 : Nat := 118140960795 + 477023 * 2 ^ 59
def prefixEnd_477023 : Nat := 4983230072969 + 3 ^ 40 * 477023 * 2
def baseEnd_477023 : Nat := 81647360749930793006239

theorem tailTrace_477023 : CollatzResearch.WordTrace tailWord_477023 prefixEnd_477023 81647360749930793006239 := by
  unfold tailWord_477023
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398458150834614887427723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11598972100556409924951815 17398458150834614887427723)
  ·
    refine ⟨26097687226251922331141585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17398458150834614887427723 26097687226251922331141585)
    ·
      refine ⟨19573265419688941748356189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26097687226251922331141585 19573265419688941748356189)
      ·
        refine ⟨7339974532383353155633571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19573265419688941748356189 7339974532383353155633571)
        ·
          refine ⟨11009961798575029733450357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339974532383353155633571 11009961798575029733450357)
          ·
            refine ⟨1032183918616409037510971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11009961798575029733450357 1032183918616409037510971)
            ·
              refine ⟨1548275877924613556266457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032183918616409037510971 1548275877924613556266457)
              ·
                refine ⟨1161206908443460167199843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548275877924613556266457 1161206908443460167199843)
                ·
                  refine ⟨1741810362665190250799765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161206908443460167199843 1741810362665190250799765)
                  ·
                    refine ⟨81647360749930793006239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1741810362665190250799765 81647360749930793006239)
                    ·
                      rfl

theorem cell23_477023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_477023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477023 prefixEnd_477023 := by exact prefixLift 477023
  have htrace : WordTrace (prefixWord ++ tailWord_477023) baseStart_477023 baseEnd_477023 := by
    simpa [prefixWord, tailWord_477023, baseEnd_477023] using wordTrace_append hprefix tailTrace_477023
  have hstable : (prefixWord ++ tailWord_477023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477023).length < 2 ^ (prefixWord ++ tailWord_477023).sum := by decide
  have hdescent : baseEnd_477023 < baseStart_477023 := by decide
  rcases family_descends (prefixWord ++ tailWord_477023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477027 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 1, 5]
def baseStart_477027 : Nat := 118140960795 + 477027 * 2 ^ 59
def prefixEnd_477027 : Nat := 4983230072969 + 3 ^ 40 * 477027 * 2
def baseEnd_477027 : Nat := 81648045390803454456233

theorem tailTrace_477027 : CollatzResearch.WordTrace tailWord_477027 prefixEnd_477027 81648045390803454456233 := by
  unfold tailWord_477027
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398604042820123570573335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11599069361880082380382223 17398604042820123570573335)
  ·
    refine ⟨26097906064230185355860003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17398604042820123570573335 26097906064230185355860003)
    ·
      refine ⟨39146859096345278033790005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097906064230185355860003 39146859096345278033790005)
      ·
        refine ⟨3670018040282369815667813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39146859096345278033790005 3670018040282369815667813)
        ·
          refine ⟨688128382552944340437715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3670018040282369815667813 688128382552944340437715)
          ·
            refine ⟨1032192573829416510656573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688128382552944340437715 1032192573829416510656573)
            ·
              refine ⟨387072215186031191496215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032192573829416510656573 387072215186031191496215)
              ·
                refine ⟨580608322779046787244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387072215186031191496215 580608322779046787244323)
                ·
                  refine ⟨870912484168570180866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580608322779046787244323 870912484168570180866485)
                  ·
                    refine ⟨81648045390803454456233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 870912484168570180866485 81648045390803454456233)
                    ·
                      rfl

theorem cell23_477027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 5].length) (baseStart_477027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477027 prefixEnd_477027 := by exact prefixLift 477027
  have htrace : WordTrace (prefixWord ++ tailWord_477027) baseStart_477027 baseEnd_477027 := by
    simpa [prefixWord, tailWord_477027, baseEnd_477027] using wordTrace_append hprefix tailTrace_477027
  have hstable : (prefixWord ++ tailWord_477027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477027).length < 2 ^ (prefixWord ++ tailWord_477027).sum := by decide
  have hdescent : baseEnd_477027 < baseStart_477027 := by decide
  rcases family_descends (prefixWord ++ tailWord_477027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477036 : List Nat := [2, 2, 1, 1, 4, 13]
def baseStart_477036 : Nat := 118140960795 + 477036 * 2 ^ 59
def prefixEnd_477036 : Nat := 4983230072969 + 3 ^ 40 * 477036 * 2
def baseEnd_477036 : Nat := 1008019578182307934799

theorem tailTrace_477036 : CollatzResearch.WordTrace tailWord_477036 prefixEnd_477036 1008019578182307934799 := by
  unfold tailWord_477036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699466149893759053825481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11599288199858345405100641 8699466149893759053825481)
  ·
    refine ⟨6524599612420319290369111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8699466149893759053825481 6524599612420319290369111)
    ·
      refine ⟨9786899418630478935553667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6524599612420319290369111 9786899418630478935553667)
      ·
        refine ⟨14680349127945718403330501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9786899418630478935553667 14680349127945718403330501)
        ·
          refine ⟨2752565461489822200624469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14680349127945718403330501 2752565461489822200624469)
          ·
            refine ⟨1008019578182307934799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 2752565461489822200624469 1008019578182307934799)
            ·
              rfl

theorem cell23_477036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 13].length) (baseStart_477036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477036 prefixEnd_477036 := by exact prefixLift 477036
  have htrace : WordTrace (prefixWord ++ tailWord_477036) baseStart_477036 baseEnd_477036 := by
    simpa [prefixWord, tailWord_477036, baseEnd_477036] using wordTrace_append hprefix tailTrace_477036
  have hstable : (prefixWord ++ tailWord_477036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477036).length < 2 ^ (prefixWord ++ tailWord_477036).sum := by decide
  have hdescent : baseEnd_477036 < baseStart_477036 := by decide
  rcases family_descends (prefixWord ++ tailWord_477036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477057 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_477057 : Nat := 118140960795 + 477057 * 2 ^ 59
def prefixEnd_477057 : Nat := 4983230072969 + 3 ^ 40 * 477057 * 2
def baseEnd_477057 : Nat := 81653180197348415331187

theorem tailTrace_477057 : CollatzResearch.WordTrace tailWord_477057 prefixEnd_477057 81653180197348415331187 := by
  unfold tailWord_477057
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399698232711438694165425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11599798821807625796110283 17399698232711438694165425)
  ·
    refine ⟨13049773674533579020624069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17399698232711438694165425 13049773674533579020624069)
    ·
      refine ⟨2446832563975046066367013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13049773674533579020624069 2446832563975046066367013)
      ·
        refine ⟨458781105745321137443815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2446832563975046066367013 458781105745321137443815)
        ·
          refine ⟨688171658617981706165723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458781105745321137443815 688171658617981706165723)
          ·
            refine ⟨1032257487926972559248585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688171658617981706165723 1032257487926972559248585)
            ·
              refine ⟨774193115945229419436439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032257487926972559248585 774193115945229419436439)
              ·
                refine ⟨1161289673917844129154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774193115945229419436439 1161289673917844129154659)
                ·
                  refine ⟨1741934510876766193731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161289673917844129154659 1741934510876766193731989)
                  ·
                    refine ⟨81653180197348415331187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1741934510876766193731989 81653180197348415331187)
                    ·
                      rfl

theorem cell23_477057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_477057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477057 prefixEnd_477057 := by exact prefixLift 477057
  have htrace : WordTrace (prefixWord ++ tailWord_477057) baseStart_477057 baseEnd_477057 := by
    simpa [prefixWord, tailWord_477057, baseEnd_477057] using wordTrace_append hprefix tailTrace_477057
  have hstable : (prefixWord ++ tailWord_477057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477057).length < 2 ^ (prefixWord ++ tailWord_477057).sum := by decide
  have hdescent : baseEnd_477057 < baseStart_477057 := by decide
  rcases family_descends (prefixWord ++ tailWord_477057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477064 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_477064 : Nat := 118140960795 + 477064 * 2 ^ 59
def prefixEnd_477064 : Nat := 4983230072969 + 3 ^ 40 * 477064 * 2
def baseEnd_477064 : Nat := 244963134956626718606029

theorem tailTrace_477064 : CollatzResearch.WordTrace tailWord_477064 prefixEnd_477064 244963134956626718606029 := by
  unfold tailWord_477064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699976771843039444835123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11599969029124052593113497 8699976771843039444835123)
  ·
    refine ⟨13049965157764559167252685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8699976771843039444835123 13049965157764559167252685)
    ·
      refine ⟨4893736934161709687719757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13049965157764559167252685 4893736934161709687719757)
      ·
        refine ⟨1835151350310641132894909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4893736934161709687719757 1835151350310641132894909)
        ·
          refine ⟨688181756366490424835591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835151350310641132894909 688181756366490424835591)
          ·
            refine ⟨1032272634549735637253387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688181756366490424835591 1032272634549735637253387)
            ·
              refine ⟨1548408951824603455880081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032272634549735637253387 1548408951824603455880081)
              ·
                refine ⟨1161306713868452591910061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548408951824603455880081 1161306713868452591910061)
                ·
                  refine ⟨435490017700669721966273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161306713868452591910061 435490017700669721966273)
                  ·
                    refine ⟨326617513275502291474705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 435490017700669721966273 326617513275502291474705)
                    ·
                      refine ⟨244963134956626718606029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326617513275502291474705 244963134956626718606029)
                      ·
                        rfl

theorem cell23_477064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_477064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477064 prefixEnd_477064 := by exact prefixLift 477064
  have htrace : WordTrace (prefixWord ++ tailWord_477064) baseStart_477064 baseEnd_477064 := by
    simpa [prefixWord, tailWord_477064, baseEnd_477064] using wordTrace_append hprefix tailTrace_477064
  have hstable : (prefixWord ++ tailWord_477064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477064).length < 2 ^ (prefixWord ++ tailWord_477064).sum := by decide
  have hdescent : baseEnd_477064 < baseStart_477064 := by decide
  rcases family_descends (prefixWord ++ tailWord_477064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477078 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_477078 : Nat := 118140960795 + 477078 * 2 ^ 59
def prefixEnd_477078 : Nat := 4983230072969 + 3 ^ 40 * 477078 * 2
def baseEnd_477078 : Nat := 81656774561929887943655

theorem tailTrace_477078 : CollatzResearch.WordTrace tailWord_477078 prefixEnd_477078 81656774561929887943655 := by
  unfold tailWord_477078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087529010352209955042493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11600309443756906187119925 1087529010352209955042493)
  ·
    refine ⟨407823378882078733140935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1087529010352209955042493 407823378882078733140935)
    ·
      refine ⟨611735068323118099711403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407823378882078733140935 611735068323118099711403)
      ·
        refine ⟨917602602484677149567105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611735068323118099711403 917602602484677149567105)
        ·
          refine ⟨688201951863507862175329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917602602484677149567105 688201951863507862175329)
          ·
            refine ⟨516151463897630896631497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688201951863507862175329 516151463897630896631497)
            ·
              refine ⟨387113597923223172473623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516151463897630896631497 387113597923223172473623)
              ·
                refine ⟨580670396884834758710435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387113597923223172473623 580670396884834758710435)
                ·
                  refine ⟨871005595327252138065653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580670396884834758710435 871005595327252138065653)
                  ·
                    refine ⟨81656774561929887943655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 871005595327252138065653 81656774561929887943655)
                    ·
                      rfl

theorem cell23_477078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_477078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477078 prefixEnd_477078 := by exact prefixLift 477078
  have htrace : WordTrace (prefixWord ++ tailWord_477078) baseStart_477078 baseEnd_477078 := by
    simpa [prefixWord, tailWord_477078, baseEnd_477078] using wordTrace_append hprefix tailTrace_477078
  have hstable : (prefixWord ++ tailWord_477078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477078).length < 2 ^ (prefixWord ++ tailWord_477078).sum := by decide
  have hdescent : baseEnd_477078 < baseStart_477078 := by decide
  rcases family_descends (prefixWord ++ tailWord_477078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477084 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_477084 : Nat := 118140960795 + 477084 * 2 ^ 59
def prefixEnd_477084 : Nat := 4983230072969 + 3 ^ 40 * 477084 * 2
def baseEnd_477084 : Nat := 244973404569716640355937

theorem tailTrace_477084 : CollatzResearch.WordTrace tailWord_477084 prefixEnd_477084 244973404569716640355937 := by
  unfold tailWord_477084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700341501806811152699153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11600455335742414870265537 8700341501806811152699153)
  ·
    refine ⟨6525256126355108364524365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8700341501806811152699153 6525256126355108364524365)
    ·
      refine ⟨2446971047383165636696637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6525256126355108364524365 2446971047383165636696637)
      ·
        refine ⟨917614142768687113761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2446971047383165636696637 917614142768687113761239)
        ·
          refine ⟨1376421214153030670641859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917614142768687113761239 1376421214153030670641859)
          ·
            refine ⟨2064631821229546005962789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376421214153030670641859 2064631821229546005962789)
            ·
              refine ⟨387118466480539876118023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2064631821229546005962789 387118466480539876118023)
              ·
                refine ⟨580677699720809814177035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387118466480539876118023 580677699720809814177035)
                ·
                  refine ⟨871016549581214721265553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580677699720809814177035 871016549581214721265553)
                  ·
                    refine ⟨653262412185911040949165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871016549581214721265553 653262412185911040949165)
                    ·
                      refine ⟨244973404569716640355937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 653262412185911040949165 244973404569716640355937)
                      ·
                        rfl

theorem cell23_477084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_477084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477084 prefixEnd_477084 := by exact prefixLift 477084
  have htrace : WordTrace (prefixWord ++ tailWord_477084) baseStart_477084 baseEnd_477084 := by
    simpa [prefixWord, tailWord_477084, baseEnd_477084] using wordTrace_append hprefix tailTrace_477084
  have hstable : (prefixWord ++ tailWord_477084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477084).length < 2 ^ (prefixWord ++ tailWord_477084).sum := by decide
  have hdescent : baseEnd_477084 < baseStart_477084 := by decide
  rcases family_descends (prefixWord ++ tailWord_477084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477113 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_477113 : Nat := 118140960795 + 477113 * 2 ^ 59
def prefixEnd_477113 : Nat := 4983230072969 + 3 ^ 40 * 477113 * 2
def baseEnd_477113 : Nat := 81662765169565675631101

theorem tailTrace_477113 : CollatzResearch.WordTrace tailWord_477113 prefixEnd_477113 81662765169565675631101 := by
  unfold tailWord_477113
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401740720508560258203993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11601160480339040172135995 17401740720508560258203993)
  ·
    refine ⟨13051305540381420193652995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17401740720508560258203993 13051305540381420193652995)
    ·
      refine ⟨19576958310572130290479493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051305540381420193652995 19576958310572130290479493)
      ·
        refine ⟨3670679683232274429464905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19576958310572130290479493 3670679683232274429464905)
        ·
          refine ⟨2753009762424205822098679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670679683232274429464905 2753009762424205822098679)
          ·
            refine ⟨4129514643636308733148019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753009762424205822098679 4129514643636308733148019)
            ·
              refine ⟨6194271965454463099722029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129514643636308733148019 6194271965454463099722029)
              ·
                refine ⟨2322851987045423662395761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6194271965454463099722029 2322851987045423662395761)
                ·
                  refine ⟨1742138990284067746796821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322851987045423662395761 1742138990284067746796821)
                  ·
                    refine ⟨81662765169565675631101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1742138990284067746796821 81662765169565675631101)
                    ·
                      rfl

theorem cell23_477113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_477113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477113 prefixEnd_477113 := by exact prefixLift 477113
  have htrace : WordTrace (prefixWord ++ tailWord_477113) baseStart_477113 baseEnd_477113 := by
    simpa [prefixWord, tailWord_477113, baseEnd_477113] using wordTrace_append hprefix tailTrace_477113
  have hstable : (prefixWord ++ tailWord_477113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477113).length < 2 ^ (prefixWord ++ tailWord_477113).sum := by decide
  have hdescent : baseEnd_477113 < baseStart_477113 := by decide
  rcases family_descends (prefixWord ++ tailWord_477113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477140 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_477140 : Nat := 118140960795 + 477140 * 2 ^ 59
def prefixEnd_477140 : Nat := 4983230072969 + 3 ^ 40 * 477140 * 2
def baseEnd_477140 : Nat := 245002159486368421255679

theorem tailTrace_477140 : CollatzResearch.WordTrace tailWord_477140 prefixEnd_477140 245002159486368421255679 := by
  unfold tailWord_477140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701362745705371934718437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11601816994273829246291249 8701362745705371934718437)
  ·
    refine ⟨1631505514819757237759707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8701362745705371934718437 1631505514819757237759707)
    ·
      refine ⟨2447258272229635856639561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1631505514819757237759707 2447258272229635856639561)
      ·
        refine ⟨1835443704172226892479671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447258272229635856639561 1835443704172226892479671)
        ·
          refine ⟨2753165556258340338719507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835443704172226892479671 2753165556258340338719507)
          ·
            refine ⟨4129748334387510508079261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753165556258340338719507 4129748334387510508079261)
            ·
              refine ⟨1548655625395316440529723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4129748334387510508079261 1548655625395316440529723)
              ·
                refine ⟨2322983438092974660794585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548655625395316440529723 2322983438092974660794585)
                ·
                  refine ⟨1742237578569730995595939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322983438092974660794585 1742237578569730995595939)
                  ·
                    refine ⟨2613356367854596493393909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1742237578569730995595939 2613356367854596493393909)
                    ·
                      refine ⟨245002159486368421255679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2613356367854596493393909 245002159486368421255679)
                      ·
                        rfl

theorem cell23_477140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_477140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477140 prefixEnd_477140 := by exact prefixLift 477140
  have htrace : WordTrace (prefixWord ++ tailWord_477140) baseStart_477140 baseEnd_477140 := by
    simpa [prefixWord, tailWord_477140, baseEnd_477140] using wordTrace_append hprefix tailTrace_477140
  have hstable : (prefixWord ++ tailWord_477140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477140).length < 2 ^ (prefixWord ++ tailWord_477140).sum := by decide
  have hdescent : baseEnd_477140 < baseStart_477140 := by decide
  rcases family_descends (prefixWord ++ tailWord_477140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477165 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_477165 : Nat := 118140960795 + 477165 * 2 ^ 59
def prefixEnd_477165 : Nat := 4983230072969 + 3 ^ 40 * 477165 * 2
def baseEnd_477165 : Nat := 245014996502730823443065

theorem tailTrace_477165 : CollatzResearch.WordTrace tailWord_477165 prefixEnd_477165 245014996502730823443065 := by
  unfold tailWord_477165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17403637316320173139096949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11602424877546782092731299 17403637316320173139096949)
  ·
    refine ⟨1631590998405016231790339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17403637316320173139096949 1631590998405016231790339)
    ·
      refine ⟨2447386497607524347685509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1631590998405016231790339 2447386497607524347685509)
      ·
        refine ⟨458884968301410815191033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2447386497607524347685509 458884968301410815191033)
        ·
          refine ⟨344163726226058111393275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458884968301410815191033 344163726226058111393275)
          ·
            refine ⟨516245589339087167089913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344163726226058111393275 516245589339087167089913)
            ·
              refine ⟨387184192004315375317435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516245589339087167089913 387184192004315375317435)
              ·
                refine ⟨580776288006473062976153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387184192004315375317435 580776288006473062976153)
                ·
                  refine ⟨435582216004854797232115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580776288006473062976153 435582216004854797232115)
                  ·
                    refine ⟨653373324007282195848173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435582216004854797232115 653373324007282195848173)
                    ·
                      refine ⟨245014996502730823443065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 653373324007282195848173 245014996502730823443065)
                      ·
                        rfl

theorem cell23_477165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_477165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477165 prefixEnd_477165 := by exact prefixLift 477165
  have htrace : WordTrace (prefixWord ++ tailWord_477165) baseStart_477165 baseEnd_477165 := by
    simpa [prefixWord, tailWord_477165, baseEnd_477165] using wordTrace_append hprefix tailTrace_477165
  have hstable : (prefixWord ++ tailWord_477165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477165).length < 2 ^ (prefixWord ++ tailWord_477165).sum := by decide
  have hdescent : baseEnd_477165 < baseStart_477165 := by decide
  rcases family_descends (prefixWord ++ tailWord_477165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477247 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_477247 : Nat := 118140960795 + 477247 * 2 ^ 59
def prefixEnd_477247 : Nat := 4983230072969 + 3 ^ 40 * 477247 * 2
def baseEnd_477247 : Nat := 245057101916399502617687

theorem tailTrace_477247 : CollatzResearch.WordTrace tailWord_477247 prefixEnd_477247 245057101916399502617687 := by
  unfold tailWord_477247
  simp only [CollatzResearch.WordTrace]
  refine ⟨17406628102023101143581995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11604418734682067429054663 17406628102023101143581995)
  ·
    refine ⟨26109942153034651715372993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17406628102023101143581995 26109942153034651715372993)
    ·
      refine ⟨19582456614775988786529745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26109942153034651715372993 19582456614775988786529745)
      ·
        refine ⟨14686842461081991589897309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19582456614775988786529745 14686842461081991589897309)
        ·
          refine ⟨5507565922905746846211491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14686842461081991589897309 5507565922905746846211491)
          ·
            refine ⟨8261348884358620269317237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507565922905746846211491 8261348884358620269317237)
            ·
              refine ⟨774501457908620650248491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8261348884358620269317237 774501457908620650248491)
              ·
                refine ⟨1161752186862930975372737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774501457908620650248491 1161752186862930975372737)
                ·
                  refine ⟨871314140147198231529553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161752186862930975372737 871314140147198231529553)
                  ·
                    refine ⟨653485605110398673647165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871314140147198231529553 653485605110398673647165)
                    ·
                      refine ⟨245057101916399502617687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 653485605110398673647165 245057101916399502617687)
                      ·
                        rfl

theorem cell23_477247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_477247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477247 prefixEnd_477247 := by exact prefixLift 477247
  have htrace : WordTrace (prefixWord ++ tailWord_477247) baseStart_477247 baseEnd_477247 := by
    simpa [prefixWord, tailWord_477247, baseEnd_477247] using wordTrace_append hprefix tailTrace_477247
  have hstable : (prefixWord ++ tailWord_477247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477247).length < 2 ^ (prefixWord ++ tailWord_477247).sum := by decide
  have hdescent : baseEnd_477247 < baseStart_477247 := by decide
  rcases family_descends (prefixWord ++ tailWord_477247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477254 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_477254 : Nat := 118140960795 + 477254 * 2 ^ 59
def prefixEnd_477254 : Nat := 4983230072969 + 3 ^ 40 * 477254 * 2
def baseEnd_477254 : Nat := 81686898760326991743385

theorem tailTrace_477254 : CollatzResearch.WordTrace tailWord_477254 prefixEnd_477254 81686898760326991743385 := by
  unfold tailWord_477254
  simp only [CollatzResearch.WordTrace]
  refine ⟨543965106656179416846463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11604588941998494226057877 543965106656179416846463)
  ·
    refine ⟨815947659984269125269695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543965106656179416846463 815947659984269125269695)
    ·
      refine ⟨1223921489976403687904543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815947659984269125269695 1223921489976403687904543)
      ·
        refine ⟨1835882234964605531856815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223921489976403687904543 1835882234964605531856815)
        ·
          refine ⟨2753823352446908297785223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835882234964605531856815 2753823352446908297785223)
          ·
            refine ⟨4130735028670362446677835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753823352446908297785223 4130735028670362446677835)
            ·
              refine ⟨6196102543005543670016753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130735028670362446677835 6196102543005543670016753)
              ·
                refine ⟨4647076907254157752512565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196102543005543670016753 4647076907254157752512565)
                ·
                  refine ⟨435663460055077289298053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647076907254157752512565 435663460055077289298053)
                  ·
                    refine ⟨81686898760326991743385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435663460055077289298053 81686898760326991743385)
                    ·
                      rfl

theorem cell23_477254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_477254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477254 prefixEnd_477254 := by exact prefixLift 477254
  have htrace : WordTrace (prefixWord ++ tailWord_477254) baseStart_477254 baseEnd_477254 := by
    simpa [prefixWord, tailWord_477254, baseEnd_477254] using wordTrace_append hprefix tailTrace_477254
  have hstable : (prefixWord ++ tailWord_477254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477254).length < 2 ^ (prefixWord ++ tailWord_477254).sum := by decide
  have hdescent : baseEnd_477254 < baseStart_477254 := by decide
  rcases family_descends (prefixWord ++ tailWord_477254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477287 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_477287 : Nat := 118140960795 + 477287 * 2 ^ 59
def prefixEnd_477287 : Nat := 4983230072969 + 3 ^ 40 * 477287 * 2
def baseEnd_477287 : Nat := 245077641142579346117503

theorem tailTrace_477287 : CollatzResearch.WordTrace tailWord_477287 prefixEnd_477287 245077641142579346117503 := by
  unfold tailWord_477287
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408087021878187975038115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11605391347918791983358743 17408087021878187975038115)
  ·
    refine ⟨26112130532817281962557173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17408087021878187975038115 26112130532817281962557173)
    ·
      refine ⟨2448012237451620183989735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26112130532817281962557173 2448012237451620183989735)
      ·
        refine ⟨3672018356177430275984603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448012237451620183989735 3672018356177430275984603)
        ·
          refine ⟨5508027534266145413976905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672018356177430275984603 5508027534266145413976905)
          ·
            refine ⟨4131020650699609060482679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508027534266145413976905 4131020650699609060482679)
            ·
              refine ⟨6196530976049413590724019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131020650699609060482679 6196530976049413590724019)
              ·
                refine ⟨9294796464074120386086029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196530976049413590724019 9294796464074120386086029)
                ·
                  refine ⟨3485548674027795144782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294796464074120386086029 3485548674027795144782261)
                  ·
                    refine ⟨326770188190105794823337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3485548674027795144782261 326770188190105794823337)
                    ·
                      refine ⟨245077641142579346117503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326770188190105794823337 245077641142579346117503)
                      ·
                        rfl

theorem cell23_477287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_477287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477287 prefixEnd_477287 := by exact prefixLift 477287
  have htrace : WordTrace (prefixWord ++ tailWord_477287) baseStart_477287 baseEnd_477287 := by
    simpa [prefixWord, tailWord_477287, baseEnd_477287] using wordTrace_append hprefix tailTrace_477287
  have hstable : (prefixWord ++ tailWord_477287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477287).length < 2 ^ (prefixWord ++ tailWord_477287).sum := by decide
  have hdescent : baseEnd_477287 < baseStart_477287 := by decide
  rcases family_descends (prefixWord ++ tailWord_477287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477294 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_477294 : Nat := 118140960795 + 477294 * 2 ^ 59
def prefixEnd_477294 : Nat := 4983230072969 + 3 ^ 40 * 477294 * 2
def baseEnd_477294 : Nat := 245081235507160818729971

theorem tailTrace_477294 : CollatzResearch.WordTrace tailWord_477294 prefixEnd_477294 245081235507160818729971 := by
  unfold tailWord_477294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176042791606603521317867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11605561555235218780361957 2176042791606603521317867)
  ·
    refine ⟨3264064187409905281976801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176042791606603521317867 3264064187409905281976801)
    ·
      refine ⟨2448048140557428961482601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3264064187409905281976801 2448048140557428961482601)
      ·
        refine ⟨1836036105418071721111951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448048140557428961482601 1836036105418071721111951)
        ·
          refine ⟨2754054158127107581667927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836036105418071721111951 2754054158127107581667927)
          ·
            refine ⟨4131081237190661372501891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754054158127107581667927 4131081237190661372501891)
            ·
              refine ⟨6196621855785992058752837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131081237190661372501891 6196621855785992058752837)
              ·
                refine ⟨1161866597959873511016157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6196621855785992058752837 1161866597959873511016157)
                ·
                  refine ⟨435699974234952566631059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1161866597959873511016157 435699974234952566631059)
                  ·
                    refine ⟨653549961352428849946589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435699974234952566631059 653549961352428849946589)
                    ·
                      refine ⟨245081235507160818729971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 653549961352428849946589 245081235507160818729971)
                      ·
                        rfl

theorem cell23_477294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_477294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477294 prefixEnd_477294 := by exact prefixLift 477294
  have htrace : WordTrace (prefixWord ++ tailWord_477294) baseStart_477294 baseEnd_477294 := by
    simpa [prefixWord, tailWord_477294, baseEnd_477294] using wordTrace_append hprefix tailTrace_477294
  have hstable : (prefixWord ++ tailWord_477294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477294).length < 2 ^ (prefixWord ++ tailWord_477294).sum := by decide
  have hdescent : baseEnd_477294 < baseStart_477294 := by decide
  rcases family_descends (prefixWord ++ tailWord_477294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477297 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_477297 : Nat := 118140960795 + 477297 * 2 ^ 59
def prefixEnd_477297 : Nat := 4983230072969 + 3 ^ 40 * 477297 * 2
def baseEnd_477297 : Nat := 81694258649708102330819

theorem tailTrace_477297 : CollatzResearch.WordTrace tailWord_477297 prefixEnd_477297 81694258649708102330819 := by
  unfold tailWord_477297
  simp only [CollatzResearch.WordTrace]
  refine ⟨17408451751841959682902145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11605634501227973121934763 17408451751841959682902145)
  ·
    refine ⟨13056338813881469762176609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17408451751841959682902145 13056338813881469762176609)
    ·
      refine ⟨9792254110411102321632457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13056338813881469762176609 9792254110411102321632457)
      ·
        refine ⟨7344190582808326741224343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792254110411102321632457 7344190582808326741224343)
        ·
          refine ⟨11016285874212490111836515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344190582808326741224343 11016285874212490111836515)
          ·
            refine ⟨16524428811318735167754773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016285874212490111836515 16524428811318735167754773)
            ·
              refine ⟨774582600530565710988505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16524428811318735167754773 774582600530565710988505)
              ·
                refine ⟨580936950397924283241379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774582600530565710988505 580936950397924283241379)
                ·
                  refine ⟨871405425596886424862069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580936950397924283241379 871405425596886424862069)
                  ·
                    refine ⟨81694258649708102330819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 871405425596886424862069 81694258649708102330819)
                    ·
                      rfl

theorem cell23_477297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_477297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477297 prefixEnd_477297 := by exact prefixLift 477297
  have htrace : WordTrace (prefixWord ++ tailWord_477297) baseStart_477297 baseEnd_477297 := by
    simpa [prefixWord, tailWord_477297, baseEnd_477297] using wordTrace_append hprefix tailTrace_477297
  have hstable : (prefixWord ++ tailWord_477297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477297).length < 2 ^ (prefixWord ++ tailWord_477297).sum := by decide
  have hdescent : baseEnd_477297 < baseStart_477297 := by decide
  rcases family_descends (prefixWord ++ tailWord_477297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477344 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_477344 : Nat := 118140960795 + 477344 * 2 ^ 59
def prefixEnd_477344 : Nat := 4983230072969 + 3 ^ 40 * 477344 * 2
def baseEnd_477344 : Nat := 81702303179961874368247

theorem tailTrace_477344 : CollatzResearch.WordTrace tailWord_477344 prefixEnd_477344 81702303179961874368247 := by
  unfold tailWord_477344
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705082991335843354931543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11606777321781124473242057 8705082991335843354931543)
  ·
    refine ⟨13057624487003765032397315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705082991335843354931543 13057624487003765032397315)
    ·
      refine ⟨19586436730505647548595973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057624487003765032397315 19586436730505647548595973)
      ·
        refine ⟨3672456886969808915361745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19586436730505647548595973 3672456886969808915361745)
        ·
          refine ⟨2754342665227356686521309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672456886969808915361745 2754342665227356686521309)
          ·
            refine ⟨1032878499460258757445491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2754342665227356686521309 1032878499460258757445491)
            ·
              refine ⟨1549317749190388136168237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032878499460258757445491 1549317749190388136168237)
              ·
                refine ⟨580994155946395551063089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1549317749190388136168237 580994155946395551063089)
                ·
                  refine ⟨435745616959796663297317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580994155946395551063089 435745616959796663297317)
                  ·
                    refine ⟨81702303179961874368247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435745616959796663297317 81702303179961874368247)
                    ·
                      rfl

theorem cell23_477344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_477344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477344 prefixEnd_477344 := by exact prefixLift 477344
  have htrace : WordTrace (prefixWord ++ tailWord_477344) baseStart_477344 baseEnd_477344 := by
    simpa [prefixWord, tailWord_477344, baseEnd_477344] using wordTrace_append hprefix tailTrace_477344
  have hstable : (prefixWord ++ tailWord_477344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477344).length < 2 ^ (prefixWord ++ tailWord_477344).sum := by decide
  have hdescent : baseEnd_477344 < baseStart_477344 := by decide
  rcases family_descends (prefixWord ++ tailWord_477344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477357 : List Nat := [1, 5, 2, 1, 2, 1, 2, 9]
def baseStart_477357 : Nat := 118140960795 + 477357 * 2 ^ 59
def prefixEnd_477357 : Nat := 4983230072969 + 3 ^ 40 * 477357 * 2
def baseEnd_477357 : Nat := 9078280918088669342303

theorem tailTrace_477357 : CollatzResearch.WordTrace tailWord_477357 prefixEnd_477357 9078280918088669342303 := by
  unfold tailWord_477357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410640131624589930086325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11607093421083059953390883 17410640131624589930086325)
  ·
    refine ⟨1632247512339805305945593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17410640131624589930086325 1632247512339805305945593)
    ·
      refine ⟨1224185634254853979459195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632247512339805305945593 1224185634254853979459195)
      ·
        refine ⟨1836278451382280969188793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224185634254853979459195 1836278451382280969188793)
        ·
          refine ⟨1377208838536710726891595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836278451382280969188793 1377208838536710726891595)
          ·
            refine ⟨2065813257805066090337393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377208838536710726891595 2065813257805066090337393)
            ·
              refine ⟨1549359943353799567753045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065813257805066090337393 1549359943353799567753045)
              ·
                refine ⟨9078280918088669342303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1549359943353799567753045 9078280918088669342303)
                ·
                  rfl

theorem cell23_477357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 9].length) (baseStart_477357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477357 prefixEnd_477357 := by exact prefixLift 477357
  have htrace : WordTrace (prefixWord ++ tailWord_477357) baseStart_477357 baseEnd_477357 := by
    simpa [prefixWord, tailWord_477357, baseEnd_477357] using wordTrace_append hprefix tailTrace_477357
  have hstable : (prefixWord ++ tailWord_477357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477357).length < 2 ^ (prefixWord ++ tailWord_477357).sum := by decide
  have hdescent : baseEnd_477357 < baseStart_477357 := by decide
  rcases family_descends (prefixWord ++ tailWord_477357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477367 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_477367 : Nat := 118140960795 + 477367 * 2 ^ 59
def prefixEnd_477367 : Nat := 4983230072969 + 3 ^ 40 * 477367 * 2
def baseEnd_477367 : Nat := 245118719594939033117135

theorem tailTrace_477367 : CollatzResearch.WordTrace tailWord_477367 prefixEnd_477367 245118719594939033117135 := by
  unfold tailWord_477367
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411004861588361637950355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11607336574392241091966903 17411004861588361637950355)
  ·
    refine ⟨26116507292382542456925533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17411004861588361637950355 26116507292382542456925533)
    ·
      refine ⟨9793690234643453421347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26116507292382542456925533 9793690234643453421347075)
      ·
        refine ⟨14690535351965180132020613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793690234643453421347075 14690535351965180132020613)
        ·
          refine ⟨2754475378493471274753865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14690535351965180132020613 2754475378493471274753865)
          ·
            refine ⟨2065856533870103456065399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754475378493471274753865 2065856533870103456065399)
            ·
              refine ⟨3098784800805155184098099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065856533870103456065399 3098784800805155184098099)
              ·
                refine ⟨4648177201207732776147149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098784800805155184098099 4648177201207732776147149)
                ·
                  refine ⟨1743066450452899791055181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648177201207732776147149 1743066450452899791055181)
                  ·
                    refine ⟨653649918919837421645693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743066450452899791055181 653649918919837421645693)
                    ·
                      refine ⟨245118719594939033117135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 653649918919837421645693 245118719594939033117135)
                      ·
                        rfl

theorem cell23_477367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_477367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477367 prefixEnd_477367 := by exact prefixLift 477367
  have htrace : WordTrace (prefixWord ++ tailWord_477367) baseStart_477367 baseEnd_477367 := by
    simpa [prefixWord, tailWord_477367, baseEnd_477367] using wordTrace_append hprefix tailTrace_477367
  have hstable : (prefixWord ++ tailWord_477367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477367).length < 2 ^ (prefixWord ++ tailWord_477367).sum := by decide
  have hdescent : baseEnd_477367 < baseStart_477367 := by decide
  rcases family_descends (prefixWord ++ tailWord_477367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477378 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_477378 : Nat := 118140960795 + 477378 * 2 ^ 59
def prefixEnd_477378 : Nat := 4983230072969 + 3 ^ 40 * 477378 * 2
def baseEnd_477378 : Nat := 81708122627379496693195

theorem tailTrace_477378 : CollatzResearch.WordTrace tailWord_477378 prefixEnd_477378 81708122627379496693195 := by
  unfold tailWord_477378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352851516137127629150197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11607604043032340344400525 4352851516137127629150197)
  ·
    refine ⟨408079829637855715232831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4352851516137127629150197 408079829637855715232831)
    ·
      refine ⟨612119744456783572849247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408079829637855715232831 612119744456783572849247)
      ·
        refine ⟨918179616685175359273871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612119744456783572849247 918179616685175359273871)
        ·
          refine ⟨1377269425027763038910807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918179616685175359273871 1377269425027763038910807)
          ·
            refine ⟨2065904137541644558366211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377269425027763038910807 2065904137541644558366211)
            ·
              refine ⟨3098856206312466837549317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065904137541644558366211 3098856206312466837549317)
              ·
                refine ⟨581035538683587532040497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3098856206312466837549317 581035538683587532040497)
                ·
                  refine ⟨435776654012690649030373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581035538683587532040497 435776654012690649030373)
                  ·
                    refine ⟨81708122627379496693195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435776654012690649030373 81708122627379496693195)
                    ·
                      rfl

theorem cell23_477378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_477378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477378 prefixEnd_477378 := by exact prefixLift 477378
  have htrace : WordTrace (prefixWord ++ tailWord_477378) baseStart_477378 baseEnd_477378 := by
    simpa [prefixWord, tailWord_477378, baseEnd_477378] using wordTrace_append hprefix tailTrace_477378
  have hstable : (prefixWord ++ tailWord_477378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477378).length < 2 ^ (prefixWord ++ tailWord_477378).sum := by decide
  have hdescent : baseEnd_477378 < baseStart_477378 := by decide
  rcases family_descends (prefixWord ++ tailWord_477378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477441 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_477441 : Nat := 118140960795 + 477441 * 2 ^ 59
def prefixEnd_477441 : Nat := 4983230072969 + 3 ^ 40 * 477441 * 2
def baseEnd_477441 : Nat := 245156717163371743591795

theorem tailTrace_477441 : CollatzResearch.WordTrace tailWord_477441 prefixEnd_477441 245156717163371743591795 := by
  unfold tailWord_477441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413703863320272276144177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11609135908880181517429451 17413703863320272276144177)
  ·
    refine ⟨13060277897490204207108133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17413703863320272276144177 13060277897490204207108133)
    ·
      refine ⟨2448802105779413288832775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13060277897490204207108133 2448802105779413288832775)
      ·
        refine ⟨3673203158669119933249163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448802105779413288832775 3673203158669119933249163)
        ·
          refine ⟨5509804738003679899873745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673203158669119933249163 5509804738003679899873745)
          ·
            refine ⟨4132353553502759924905309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509804738003679899873745 4132353553502759924905309)
            ·
              refine ⟨1549632582563534971839491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132353553502759924905309 1549632582563534971839491)
              ·
                refine ⟨2324448873845302457759237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549632582563534971839491 2324448873845302457759237)
                ·
                  refine ⟨435834163845994210829857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324448873845302457759237 435834163845994210829857)
                  ·
                    refine ⟨326875622884495658122393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 435834163845994210829857 326875622884495658122393)
                    ·
                      refine ⟨245156717163371743591795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 326875622884495658122393 245156717163371743591795)
                      ·
                        rfl

theorem cell23_477441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_477441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477441 prefixEnd_477441 := by exact prefixLift 477441
  have htrace : WordTrace (prefixWord ++ tailWord_477441) baseStart_477441 baseEnd_477441 := by
    simpa [prefixWord, tailWord_477441, baseEnd_477441] using wordTrace_append hprefix tailTrace_477441
  have hstable : (prefixWord ++ tailWord_477441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477441).length < 2 ^ (prefixWord ++ tailWord_477441).sum := by decide
  have hdescent : baseEnd_477441 < baseStart_477441 := by decide
  rcases family_descends (prefixWord ++ tailWord_477441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477554 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_477554 : Nat := 118140960795 + 477554 * 2 ^ 59
def prefixEnd_477554 : Nat := 4983230072969 + 3 ^ 40 * 477554 * 2
def baseEnd_477554 : Nat := 27246082275258866830975

theorem tailTrace_477554 : CollatzResearch.WordTrace tailWord_477554 prefixEnd_477554 27246082275258866830975 := by
  unfold tailWord_477554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354456327977723143751929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11611883541273928383338477 4354456327977723143751929)
  ·
    refine ⟨3265842245983292357813947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4354456327977723143751929 3265842245983292357813947)
    ·
      refine ⟨4898763368974938536720921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265842245983292357813947 4898763368974938536720921)
      ·
        refine ⟨3674072526731203902540691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898763368974938536720921 3674072526731203902540691)
        ·
          refine ⟨5511108790096805853811037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674072526731203902540691 5511108790096805853811037)
          ·
            refine ⟨2066665796286302195179139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5511108790096805853811037 2066665796286302195179139)
            ·
              refine ⟨3099998694429453292768709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066665796286302195179139 3099998694429453292768709)
              ·
                refine ⟨581249755205522492394133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3099998694429453292768709 581249755205522492394133)
                ·
                  refine ⟨27246082275258866830975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 581249755205522492394133 27246082275258866830975)
                  ·
                    rfl

theorem cell23_477554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_477554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477554 prefixEnd_477554 := by exact prefixLift 477554
  have htrace : WordTrace (prefixWord ++ tailWord_477554) baseStart_477554 baseEnd_477554 := by
    simpa [prefixWord, tailWord_477554, baseEnd_477554] using wordTrace_append hprefix tailTrace_477554
  have hstable : (prefixWord ++ tailWord_477554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477554).length < 2 ^ (prefixWord ++ tailWord_477554).sum := by decide
  have hdescent : baseEnd_477554 < baseStart_477554 := by decide
  rcases family_descends (prefixWord ++ tailWord_477554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477641 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_477641 : Nat := 118140960795 + 477641 * 2 ^ 59
def prefixEnd_477641 : Nat := 4983230072969 + 3 ^ 40 * 477641 * 2
def baseEnd_477641 : Nat := 245259413294270961090875

theorem tailTrace_477641 : CollatzResearch.WordTrace tailWord_477641 prefixEnd_477641 245259413294270961090875 := by
  unfold tailWord_477641
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420998462595706433424777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11613998975063804288949851 17420998462595706433424777)
  ·
    refine ⟨13065748846946779825068583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17420998462595706433424777 13065748846946779825068583)
    ·
      refine ⟨19598623270420169737602875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065748846946779825068583 19598623270420169737602875)
      ·
        refine ⟨29397934905630254606404313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598623270420169737602875 29397934905630254606404313)
        ·
          refine ⟨22048451179222690954803235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29397934905630254606404313 22048451179222690954803235)
          ·
            refine ⟨33072676768834036432204853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22048451179222690954803235 33072676768834036432204853)
            ·
              refine ⟨3100563447078190915519205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33072676768834036432204853 3100563447078190915519205)
              ·
                refine ⟨581355646327160796659851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3100563447078190915519205 581355646327160796659851)
                ·
                  refine ⟨872033469490741194989777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581355646327160796659851 872033469490741194989777)
                  ·
                    refine ⟨654025102118055896242333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872033469490741194989777 654025102118055896242333)
                    ·
                      refine ⟨245259413294270961090875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654025102118055896242333 245259413294270961090875)
                      ·
                        rfl

theorem cell23_477641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_477641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477641 prefixEnd_477641 := by exact prefixLift 477641
  have htrace : WordTrace (prefixWord ++ tailWord_477641) baseStart_477641 baseEnd_477641 := by
    simpa [prefixWord, tailWord_477641, baseEnd_477641] using wordTrace_append hprefix tailTrace_477641
  have hstable : (prefixWord ++ tailWord_477641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477641).length < 2 ^ (prefixWord ++ tailWord_477641).sum := by decide
  have hdescent : baseEnd_477641 < baseStart_477641 := by decide
  rcases family_descends (prefixWord ++ tailWord_477641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477666 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_477666 : Nat := 118140960795 + 477666 * 2 ^ 59
def prefixEnd_477666 : Nat := 4983230072969 + 3 ^ 40 * 477666 * 2
def baseEnd_477666 : Nat := 245272250310633363278261

theorem tailTrace_477666 : CollatzResearch.WordTrace tailWord_477666 prefixEnd_477666 245272250310633363278261 := by
  unfold tailWord_477666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355477571876283925771213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11614606858336757135389901 4355477571876283925771213)
  ·
    refine ⟨1633304089453606472164205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4355477571876283925771213 1633304089453606472164205)
    ·
      refine ⟨612489033545102427061577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1633304089453606472164205 612489033545102427061577)
      ·
        refine ⟨459366775158826820296183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612489033545102427061577 459366775158826820296183)
        ·
          refine ⟨689050162738240230444275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459366775158826820296183 689050162738240230444275)
          ·
            refine ⟨1033575244107360345666413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689050162738240230444275 1033575244107360345666413)
            ·
              refine ⟨387590716540260129624905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033575244107360345666413 387590716540260129624905)
              ·
                refine ⟨290693037405195097218679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387590716540260129624905 290693037405195097218679)
                ·
                  refine ⟨436039556107792645828019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290693037405195097218679 436039556107792645828019)
                  ·
                    refine ⟨654059334161688968742029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436039556107792645828019 654059334161688968742029)
                    ·
                      refine ⟨245272250310633363278261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654059334161688968742029 245272250310633363278261)
                      ·
                        rfl

theorem cell23_477666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_477666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477666 prefixEnd_477666 := by exact prefixLift 477666
  have htrace : WordTrace (prefixWord ++ tailWord_477666) baseStart_477666 baseEnd_477666 := by
    simpa [prefixWord, tailWord_477666, baseEnd_477666] using wordTrace_append hprefix tailTrace_477666
  have hstable : (prefixWord ++ tailWord_477666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477666).length < 2 ^ (prefixWord ++ tailWord_477666).sum := by decide
  have hdescent : baseEnd_477666 < baseStart_477666 := by decide
  rcases family_descends (prefixWord ++ tailWord_477666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477682 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_477682 : Nat := 118140960795 + 477682 * 2 ^ 59
def prefixEnd_477682 : Nat := 4983230072969 + 3 ^ 40 * 477682 * 2
def baseEnd_477682 : Nat := 81760155333701766892729

theorem tailTrace_477682 : CollatzResearch.WordTrace tailWord_477682 prefixEnd_477682 81760155333701766892729 := by
  unfold tailWord_477682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355623463861792608916825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11614995903631446957111533 4355623463861792608916825)
  ·
    refine ⟨3266717597896344456687619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4355623463861792608916825 3266717597896344456687619)
    ·
      refine ⟨4900076396844516685031429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266717597896344456687619 4900076396844516685031429)
      ·
        refine ⟨918764324408346878443393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4900076396844516685031429 918764324408346878443393)
        ·
          refine ⟨689073243306260158832545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918764324408346878443393 689073243306260158832545)
          ·
            refine ⟨516804932479695119124409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689073243306260158832545 516804932479695119124409)
            ·
              refine ⟨387603699359771339343307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516804932479695119124409 387603699359771339343307)
              ·
                refine ⟨581405549039657009014961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387603699359771339343307 581405549039657009014961)
                ·
                  refine ⟨436054161779742756761221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581405549039657009014961 436054161779742756761221)
                  ·
                    refine ⟨81760155333701766892729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436054161779742756761221 81760155333701766892729)
                    ·
                      rfl

theorem cell23_477682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_477682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477682 prefixEnd_477682 := by exact prefixLift 477682
  have htrace : WordTrace (prefixWord ++ tailWord_477682) baseStart_477682 baseEnd_477682 := by
    simpa [prefixWord, tailWord_477682, baseEnd_477682] using wordTrace_append hprefix tailTrace_477682
  have hstable : (prefixWord ++ tailWord_477682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477682).length < 2 ^ (prefixWord ++ tailWord_477682).sum := by decide
  have hdescent : baseEnd_477682 < baseStart_477682 := by decide
  rcases family_descends (prefixWord ++ tailWord_477682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477688 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_477688 : Nat := 118140960795 + 477688 * 2 ^ 59
def prefixEnd_477688 : Nat := 4983230072969 + 3 ^ 40 * 477688 * 2
def baseEnd_477688 : Nat := 245283546885032277203159

theorem tailTrace_477688 : CollatzResearch.WordTrace tailWord_477688 prefixEnd_477688 245283546885032277203159 := by
  unfold tailWord_477688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711356346712716730192859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11615141795616955640257145 8711356346712716730192859)
  ·
    refine ⟨13067034520069075095289289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8711356346712716730192859 13067034520069075095289289)
    ·
      refine ⟨9800275890051806321466967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13067034520069075095289289 9800275890051806321466967)
      ·
        refine ⟨14700413835077709482200451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9800275890051806321466967 14700413835077709482200451)
        ·
          refine ⟨22050620752616564223300677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14700413835077709482200451 22050620752616564223300677)
          ·
            refine ⟨4134491391115605791868877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22050620752616564223300677 4134491391115605791868877)
            ·
              refine ⟨1550434271668352171950829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4134491391115605791868877 1550434271668352171950829)
              ·
                refine ⟨581412851875632064481561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1550434271668352171950829 581412851875632064481561)
                ·
                  refine ⟨436059638906724048361171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581412851875632064481561 436059638906724048361171)
                  ·
                    refine ⟨654089458360086072541757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436059638906724048361171 654089458360086072541757)
                    ·
                      refine ⟨245283546885032277203159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654089458360086072541757 245283546885032277203159)
                      ·
                        rfl

theorem cell23_477688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_477688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477688 prefixEnd_477688 := by exact prefixLift 477688
  have htrace : WordTrace (prefixWord ++ tailWord_477688) baseStart_477688 baseEnd_477688 := by
    simpa [prefixWord, tailWord_477688, baseEnd_477688] using wordTrace_append hprefix tailTrace_477688
  have hstable : (prefixWord ++ tailWord_477688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477688).length < 2 ^ (prefixWord ++ tailWord_477688).sum := by decide
  have hdescent : baseEnd_477688 < baseStart_477688 := by decide
  rcases family_descends (prefixWord ++ tailWord_477688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477702 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_477702 : Nat := 118140960795 + 477702 * 2 ^ 59
def prefixEnd_477702 : Nat := 4983230072969 + 3 ^ 40 * 477702 * 2
def baseEnd_477702 : Nat := 245290735614195222428095

theorem tailTrace_477702 : CollatzResearch.WordTrace tailWord_477702 prefixEnd_477702 245290735614195222428095 := by
  unfold tailWord_477702
  simp only [CollatzResearch.WordTrace]
  refine ⟨544475728605459807856105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11615482210249809234263573 544475728605459807856105)
  ·
    refine ⟨408356796454094855892079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 544475728605459807856105 408356796454094855892079)
    ·
      refine ⟨612535194681142283838119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408356796454094855892079 612535194681142283838119)
      ·
        refine ⟨918802792021713425757179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612535194681142283838119 918802792021713425757179)
        ·
          refine ⟨1378204188032570138635769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918802792021713425757179 1378204188032570138635769)
          ·
            refine ⟨1033653141024427603976827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378204188032570138635769 1033653141024427603976827)
            ·
              refine ⟨1550479711536641405965241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033653141024427603976827 1550479711536641405965241)
              ·
                refine ⟨1162859783652481054473931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550479711536641405965241 1162859783652481054473931)
                ·
                  refine ⟨1744289675478721581710897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162859783652481054473931 1744289675478721581710897)
                  ·
                    refine ⟨1308217256609041186283173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1744289675478721581710897 1308217256609041186283173)
                    ·
                      refine ⟨245290735614195222428095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1308217256609041186283173 245290735614195222428095)
                      ·
                        rfl

theorem cell23_477702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_477702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477702 prefixEnd_477702 := by exact prefixLift 477702
  have htrace : WordTrace (prefixWord ++ tailWord_477702) baseStart_477702 baseEnd_477702 := by
    simpa [prefixWord, tailWord_477702, baseEnd_477702] using wordTrace_append hprefix tailTrace_477702
  have hstable : (prefixWord ++ tailWord_477702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477702).length < 2 ^ (prefixWord ++ tailWord_477702).sum := by decide
  have hdescent : baseEnd_477702 < baseStart_477702 := by decide
  rcases family_descends (prefixWord ++ tailWord_477702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477704 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_477704 : Nat := 118140960795 + 477704 * 2 ^ 59
def prefixEnd_477704 : Nat := 4983230072969 + 3 ^ 40 * 477704 * 2
def baseEnd_477704 : Nat := 81763920858501404867695

theorem tailTrace_477704 : CollatzResearch.WordTrace tailWord_477704 prefixEnd_477704 81763920858501404867695 := by
  unfold tailWord_477704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711648130683734096484083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11615530840911645461978777 8711648130683734096484083)
  ·
    refine ⟨13067472196025601144726125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8711648130683734096484083 13067472196025601144726125)
    ·
      refine ⟨4900302073509600429272297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13067472196025601144726125 4900302073509600429272297)
      ·
        refine ⟨3675226555132200321954223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900302073509600429272297 3675226555132200321954223)
        ·
          refine ⟨5512839832698300482931335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675226555132200321954223 5512839832698300482931335)
          ·
            refine ⟨8269259749047450724397003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512839832698300482931335 8269259749047450724397003)
            ·
              refine ⟨12403889623571176086595505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269259749047450724397003 12403889623571176086595505)
              ·
                refine ⟨9302917217678382064946629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403889623571176086595505 9302917217678382064946629)
                ·
                  refine ⟨1744296978314696637177493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9302917217678382064946629 1744296978314696637177493)
                  ·
                    refine ⟨81763920858501404867695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1744296978314696637177493 81763920858501404867695)
                    ·
                      rfl

theorem cell23_477704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_477704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477704 prefixEnd_477704 := by exact prefixLift 477704
  have htrace : WordTrace (prefixWord ++ tailWord_477704) baseStart_477704 baseEnd_477704 := by
    simpa [prefixWord, tailWord_477704, baseEnd_477704] using wordTrace_append hprefix tailTrace_477704
  have hstable : (prefixWord ++ tailWord_477704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477704).length < 2 ^ (prefixWord ++ tailWord_477704).sum := by decide
  have hdescent : baseEnd_477704 < baseStart_477704 := by decide
  rcases family_descends (prefixWord ++ tailWord_477704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477709 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_477709 : Nat := 118140960795 + 477709 * 2 ^ 59
def prefixEnd_477709 : Nat := 4983230072969 + 3 ^ 40 * 477709 * 2
def baseEnd_477709 : Nat := 245294329978776695040563

theorem tailTrace_477709 : CollatzResearch.WordTrace tailWord_477709 prefixEnd_477709 245294329978776695040563 := by
  unfold tailWord_477709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423478626349354046900181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11615652417566236031266787 17423478626349354046900181)
  ·
    refine ⟨408362780305062985474223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17423478626349354046900181 408362780305062985474223)
    ·
      refine ⟨612544170457594478211335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408362780305062985474223 612544170457594478211335)
      ·
        refine ⟨918816255686391717317003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612544170457594478211335 918816255686391717317003)
        ·
          refine ⟨1378224383529587575975505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918816255686391717317003 1378224383529587575975505)
          ·
            refine ⟨1033668287647190681981629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378224383529587575975505 1033668287647190681981629)
            ·
              refine ⟨387625607867696505743111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033668287647190681981629 387625607867696505743111)
              ·
                refine ⟨581438411801544758614667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387625607867696505743111 581438411801544758614667)
                ·
                  refine ⟨872157617702317137922001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581438411801544758614667 872157617702317137922001)
                  ·
                    refine ⟨654118213276737853441501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872157617702317137922001 654118213276737853441501)
                    ·
                      refine ⟨245294329978776695040563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654118213276737853441501 245294329978776695040563)
                      ·
                        rfl

theorem cell23_477709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_477709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477709 prefixEnd_477709 := by exact prefixLift 477709
  have htrace : WordTrace (prefixWord ++ tailWord_477709) baseStart_477709 baseEnd_477709 := by
    simpa [prefixWord, tailWord_477709, baseEnd_477709] using wordTrace_append hprefix tailTrace_477709
  have hstable : (prefixWord ++ tailWord_477709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477709).length < 2 ^ (prefixWord ++ tailWord_477709).sum := by decide
  have hdescent : baseEnd_477709 < baseStart_477709 := by decide
  rcases family_descends (prefixWord ++ tailWord_477709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 4, 2]
def baseStart_477711 : Nat := 118140960795 + 477711 * 2 ^ 59
def prefixEnd_477711 : Nat := 4983230072969 + 3 ^ 40 * 477711 * 2
def baseEnd_477711 : Nat := 245295356940085687215553

theorem tailTrace_477711 : CollatzResearch.WordTrace tailWord_477711 prefixEnd_477711 245295356940085687215553 := by
  unfold tailWord_477711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423551572342108388472987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11615701048228072258981991 17423551572342108388472987)
  ·
    refine ⟨26135327358513162582709481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17423551572342108388472987 26135327358513162582709481)
    ·
      refine ⟨19601495518884871937032111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26135327358513162582709481 19601495518884871937032111)
      ·
        refine ⟨29402243278327307905548167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19601495518884871937032111 29402243278327307905548167)
        ·
          refine ⟨44103364917490961858322251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29402243278327307905548167 44103364917490961858322251)
          ·
            refine ⟨66155047376236442787483377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44103364917490961858322251 66155047376236442787483377)
            ·
              refine ⟨49616285532177332090612533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66155047376236442787483377 49616285532177332090612533)
              ·
                refine ⟨4651526768641624883494925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49616285532177332090612533 4651526768641624883494925)
                ·
                  refine ⟨1744322538240609331310597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4651526768641624883494925 1744322538240609331310597)
                  ·
                    refine ⟨327060475920114249620737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744322538240609331310597 327060475920114249620737)
                    ·
                      refine ⟨245295356940085687215553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327060475920114249620737 245295356940085687215553)
                      ·
                        rfl

theorem cell23_477711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4, 2].length) (baseStart_477711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477711 prefixEnd_477711 := by exact prefixLift 477711
  have htrace : WordTrace (prefixWord ++ tailWord_477711) baseStart_477711 baseEnd_477711 := by
    simpa [prefixWord, tailWord_477711, baseEnd_477711] using wordTrace_append hprefix tailTrace_477711
  have hstable : (prefixWord ++ tailWord_477711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477711).length < 2 ^ (prefixWord ++ tailWord_477711).sum := by decide
  have hdescent : baseEnd_477711 < baseStart_477711 := by decide
  rcases family_descends (prefixWord ++ tailWord_477711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477715 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 1, 3, 2]
def baseStart_477715 : Nat := 118140960795 + 477715 * 2 ^ 59
def prefixEnd_477715 : Nat := 4983230072969 + 3 ^ 40 * 477715 * 2
def baseEnd_477715 : Nat := 245297410862703671565535

theorem tailTrace_477715 : CollatzResearch.WordTrace tailWord_477715 prefixEnd_477715 245297410862703671565535 := by
  unfold tailWord_477715
  simp only [CollatzResearch.WordTrace]
  refine ⟨17423697464327617071618599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11615798309551744714412399 17423697464327617071618599)
  ·
    refine ⟨26135546196491425607427899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17423697464327617071618599 26135546196491425607427899)
    ·
      refine ⟨39203319294737138411141849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26135546196491425607427899 39203319294737138411141849)
      ·
        refine ⟨29402489471052853808356387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39203319294737138411141849 29402489471052853808356387)
        ·
          refine ⟨44103734206579280712534581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29402489471052853808356387 44103734206579280712534581)
          ·
            refine ⟨4134725081866807566800117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44103734206579280712534581 4134725081866807566800117)
            ·
              refine ⟨387630476425013209387511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4134725081866807566800117 387630476425013209387511)
              ·
                refine ⟨581445714637519814081267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387630476425013209387511 581445714637519814081267)
                ·
                  refine ⟨872168571956279721121901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581445714637519814081267 872168571956279721121901)
                  ·
                    refine ⟨327063214483604895420713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872168571956279721121901 327063214483604895420713)
                    ·
                      refine ⟨245297410862703671565535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327063214483604895420713 245297410862703671565535)
                      ·
                        rfl

theorem cell23_477715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 3, 2].length) (baseStart_477715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477715 prefixEnd_477715 := by exact prefixLift 477715
  have htrace : WordTrace (prefixWord ++ tailWord_477715) baseStart_477715 baseEnd_477715 := by
    simpa [prefixWord, tailWord_477715, baseEnd_477715] using wordTrace_append hprefix tailTrace_477715
  have hstable : (prefixWord ++ tailWord_477715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477715).length < 2 ^ (prefixWord ++ tailWord_477715).sum := by decide
  have hdescent : baseEnd_477715 < baseStart_477715 := by decide
  rcases family_descends (prefixWord ++ tailWord_477715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477731 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3]
def baseStart_477731 : Nat := 118140960795 + 477731 * 2 ^ 59
def prefixEnd_477731 : Nat := 4983230072969 + 3 ^ 40 * 477731 * 2
def baseEnd_477731 : Nat := 245305626553175608965461

theorem tailTrace_477731 : CollatzResearch.WordTrace tailWord_477731 prefixEnd_477731 245305626553175608965461 := by
  unfold tailWord_477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424281032269651804201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11616187354846434536134031 17424281032269651804201047)
  ·
    refine ⟨26136421548404477706301571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424281032269651804201047 26136421548404477706301571)
    ·
      refine ⟨39204632322606716559452357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136421548404477706301571 39204632322606716559452357)
      ·
        refine ⟨7350868560488759354897317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39204632322606716559452357 7350868560488759354897317)
        ·
          refine ⟨1378287855091642379043247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7350868560488759354897317 1378287855091642379043247)
          ·
            refine ⟨2067431782637463568564871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378287855091642379043247 2067431782637463568564871)
            ·
              refine ⟨3101147673956195352847307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067431782637463568564871 3101147673956195352847307)
              ·
                refine ⟨4651721510934293029270961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101147673956195352847307 4651721510934293029270961)
                ·
                  refine ⟨3488791133200719771953221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651721510934293029270961 3488791133200719771953221)
                  ·
                    refine ⟨654148337475134957241229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488791133200719771953221 654148337475134957241229)
                    ·
                      refine ⟨245305626553175608965461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654148337475134957241229 245305626553175608965461)
                      ·
                        rfl

theorem cell23_477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_477731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477731 prefixEnd_477731 := by exact prefixLift 477731
  have htrace : WordTrace (prefixWord ++ tailWord_477731) baseStart_477731 baseEnd_477731 := by
    simpa [prefixWord, tailWord_477731, baseEnd_477731] using wordTrace_append hprefix tailTrace_477731
  have hstable : (prefixWord ++ tailWord_477731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477731).length < 2 ^ (prefixWord ++ tailWord_477731).sum := by decide
  have hdescent : baseEnd_477731 < baseStart_477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477745 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_477745 : Nat := 118140960795 + 477745 * 2 ^ 59
def prefixEnd_477745 : Nat := 4983230072969 + 3 ^ 40 * 477745 * 2
def baseEnd_477745 : Nat := 245312815282338554190397

theorem tailTrace_477745 : CollatzResearch.WordTrace tailWord_477745 prefixEnd_477745 245312815282338554190397 := by
  unfold tailWord_477745
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424791654218932195210689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11616527769479288130140459 17424791654218932195210689)
  ·
    refine ⟨13068593740664199146408017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17424791654218932195210689 13068593740664199146408017)
    ·
      refine ⟨9801445305498149359806013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13068593740664199146408017 9801445305498149359806013)
      ·
        refine ⟨3675541989561806009927255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9801445305498149359806013 3675541989561806009927255)
        ·
          refine ⟨5513312984342709014890883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675541989561806009927255 5513312984342709014890883)
          ·
            refine ⟨8269969476514063522336325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513312984342709014890883 8269969476514063522336325)
            ·
              refine ⟨1550619276846386910438061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8269969476514063522336325 1550619276846386910438061)
              ·
                refine ⟨581482228817395091414273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1550619276846386910438061 581482228817395091414273)
                ·
                  refine ⟨436111671613046318560705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581482228817395091414273 436111671613046318560705)
                  ·
                    refine ⟨327083753709784738920529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436111671613046318560705 327083753709784738920529)
                    ·
                      refine ⟨245312815282338554190397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327083753709784738920529 245312815282338554190397)
                      ·
                        rfl

theorem cell23_477745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_477745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477745 prefixEnd_477745 := by exact prefixLift 477745
  have htrace : WordTrace (prefixWord ++ tailWord_477745) baseStart_477745 baseEnd_477745 := by
    simpa [prefixWord, tailWord_477745, baseEnd_477745] using wordTrace_append hprefix tailTrace_477745
  have hstable : (prefixWord ++ tailWord_477745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477745).length < 2 ^ (prefixWord ++ tailWord_477745).sum := by decide
  have hdescent : baseEnd_477745 < baseStart_477745 := by decide
  rcases family_descends (prefixWord ++ tailWord_477745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477766 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_477766 : Nat := 118140960795 + 477766 * 2 ^ 59
def prefixEnd_477766 : Nat := 4983230072969 + 3 ^ 40 * 477766 * 2
def baseEnd_477766 : Nat := 245323598376082972027801

theorem tailTrace_477766 : CollatzResearch.WordTrace tailWord_477766 prefixEnd_477766 245323598376082972027801 := by
  unfold tailWord_477766
  simp only [CollatzResearch.WordTrace]
  refine ⟨544548674598214149428911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11617038391428568521150101 544548674598214149428911)
  ·
    refine ⟨816823011897321224143367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 544548674598214149428911 816823011897321224143367)
    ·
      refine ⟨1225234517845981836215051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816823011897321224143367 1225234517845981836215051)
      ·
        refine ⟨1837851776768972754322577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225234517845981836215051 1837851776768972754322577)
        ·
          refine ⟨1378388832576729565741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837851776768972754322577 1378388832576729565741933)
          ·
            refine ⟨516895812216273587153225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1378388832576729565741933 516895812216273587153225)
            ·
              refine ⟨387671859162205190364919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516895812216273587153225 387671859162205190364919)
              ·
                refine ⟨581507788743307785547379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387671859162205190364919 581507788743307785547379)
                ·
                  refine ⟨872261683114961678321069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581507788743307785547379 872261683114961678321069)
                  ·
                    refine ⟨327098131168110629370401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872261683114961678321069 327098131168110629370401)
                    ·
                      refine ⟨245323598376082972027801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327098131168110629370401 245323598376082972027801)
                      ·
                        rfl

theorem cell23_477766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_477766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477766 prefixEnd_477766 := by exact prefixLift 477766
  have htrace : WordTrace (prefixWord ++ tailWord_477766) baseStart_477766 baseEnd_477766 := by
    simpa [prefixWord, tailWord_477766, baseEnd_477766] using wordTrace_append hprefix tailTrace_477766
  have hstable : (prefixWord ++ tailWord_477766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477766).length < 2 ^ (prefixWord ++ tailWord_477766).sum := by decide
  have hdescent : baseEnd_477766 < baseStart_477766 := by decide
  rcases family_descends (prefixWord ++ tailWord_477766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477781 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_477781 : Nat := 118140960795 + 477781 * 2 ^ 59
def prefixEnd_477781 : Nat := 4983230072969 + 3 ^ 40 * 477781 * 2
def baseEnd_477781 : Nat := 81777100195300137780077

theorem tailTrace_477781 : CollatzResearch.WordTrace tailWord_477781 prefixEnd_477781 81777100195300137780077 := by
  unfold tailWord_477781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17426104682088510343521197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11617403121392340229014131 17426104682088510343521197)
  ·
    refine ⟨6534789255783191378820449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17426104682088510343521197 6534789255783191378820449)
    ·
      refine ⟨4901091941837393534115337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6534789255783191378820449 4901091941837393534115337)
      ·
        refine ⟨3675818956378045150586503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4901091941837393534115337 3675818956378045150586503)
        ·
          refine ⟨5513728434567067725879755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675818956378045150586503 5513728434567067725879755)
          ·
            refine ⟨8270592651850601588819633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513728434567067725879755 8270592651850601588819633)
            ·
              refine ⟨6202944488887951191614725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8270592651850601588819633 6202944488887951191614725)
              ·
                refine ⟨1163052091666490848427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6202944488887951191614725 1163052091666490848427761)
                ·
                  refine ⟨872289068749868136320821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163052091666490848427761 872289068749868136320821)
                  ·
                    refine ⟨81777100195300137780077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 872289068749868136320821 81777100195300137780077)
                    ·
                      rfl

theorem cell23_477781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_477781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477781 prefixEnd_477781 := by exact prefixLift 477781
  have htrace : WordTrace (prefixWord ++ tailWord_477781) baseStart_477781 baseEnd_477781 := by
    simpa [prefixWord, tailWord_477781, baseEnd_477781] using wordTrace_append hprefix tailTrace_477781
  have hstable : (prefixWord ++ tailWord_477781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477781).length < 2 ^ (prefixWord ++ tailWord_477781).sum := by decide
  have hdescent : baseEnd_477781 < baseStart_477781 := by decide
  rcases family_descends (prefixWord ++ tailWord_477781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477811 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 5, 4]
def baseStart_477811 : Nat := 118140960795 + 477811 * 2 ^ 59
def prefixEnd_477811 : Nat := 4983230072969 + 3 ^ 40 * 477811 * 2
def baseEnd_477811 : Nat := 81782235001845098655031

theorem tailTrace_477811 : CollatzResearch.WordTrace tailWord_477811 prefixEnd_477811 81782235001845098655031 := by
  unfold tailWord_477811
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427198871979825467113287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11618132581319883644742191 17427198871979825467113287)
  ·
    refine ⟨26140798307969738200669931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427198871979825467113287 26140798307969738200669931)
    ·
      refine ⟨39211197461954607301004897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26140798307969738200669931 39211197461954607301004897)
      ·
        refine ⟨29408398096465955475753673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39211197461954607301004897 29408398096465955475753673)
        ·
          refine ⟨22056298572349466606815255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29408398096465955475753673 22056298572349466606815255)
          ·
            refine ⟨33084447858524199910222883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22056298572349466606815255 33084447858524199910222883)
            ·
              refine ⟨49626671787786299865334325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33084447858524199910222883 49626671787786299865334325)
              ·
                refine ⟨4652500480104965612375093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49626671787786299865334325 4652500480104965612375093)
                ·
                  refine ⟨436171920009840526160165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4652500480104965612375093 436171920009840526160165)
                  ·
                    refine ⟨81782235001845098655031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436171920009840526160165 81782235001845098655031)
                    ·
                      rfl

theorem cell23_477811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 4].length) (baseStart_477811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477811 prefixEnd_477811 := by exact prefixLift 477811
  have htrace : WordTrace (prefixWord ++ tailWord_477811) baseStart_477811 baseEnd_477811 := by
    simpa [prefixWord, tailWord_477811, baseEnd_477811] using wordTrace_append hprefix tailTrace_477811
  have hstable : (prefixWord ++ tailWord_477811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477811).length < 2 ^ (prefixWord ++ tailWord_477811).sum := by decide
  have hdescent : baseEnd_477811 < baseStart_477811 := by decide
  rcases family_descends (prefixWord ++ tailWord_477811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477942 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_477942 : Nat := 118140960795 + 477942 * 2 ^ 59
def prefixEnd_477942 : Nat := 4983230072969 + 3 ^ 40 * 477942 * 2
def baseEnd_477942 : Nat := 245413970971274283426991

theorem tailTrace_477942 : CollatzResearch.WordTrace tailWord_477942 prefixEnd_477942 245413970971274283426991 := by
  unfold tailWord_477942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089498552156577177508255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11621317889670156560088053 1089498552156577177508255)
  ·
    refine ⟨1634247828234865766262383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089498552156577177508255 1634247828234865766262383)
    ·
      refine ⟨2451371742352298649393575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634247828234865766262383 2451371742352298649393575)
      ·
        refine ⟨3677057613528447974090363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451371742352298649393575 3677057613528447974090363)
        ·
          refine ⟨5515586420292671961135545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677057613528447974090363 5515586420292671961135545)
          ·
            refine ⟨4136689815219503970851659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515586420292671961135545 4136689815219503970851659)
            ·
              refine ⟨6205034722829255956277489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136689815219503970851659 6205034722829255956277489)
              ·
                refine ⟨4653776042121941967208117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205034722829255956277489 4653776042121941967208117)
                ·
                  refine ⟨436291503948932059425761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653776042121941967208117 436291503948932059425761)
                  ·
                    refine ⟨327218627961699044569321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436291503948932059425761 327218627961699044569321)
                    ·
                      refine ⟨245413970971274283426991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327218627961699044569321 245413970971274283426991)
                      ·
                        rfl

theorem cell23_477942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_477942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477942 prefixEnd_477942 := by exact prefixLift 477942
  have htrace : WordTrace (prefixWord ++ tailWord_477942) baseStart_477942 baseEnd_477942 := by
    simpa [prefixWord, tailWord_477942, baseEnd_477942] using wordTrace_append hprefix tailTrace_477942
  have hstable : (prefixWord ++ tailWord_477942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477942).length < 2 ^ (prefixWord ++ tailWord_477942).sum := by decide
  have hdescent : baseEnd_477942 < baseStart_477942 := by decide
  rcases family_descends (prefixWord ++ tailWord_477942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_477951 : Nat := 118140960795 + 477951 * 2 ^ 59
def prefixEnd_477951 : Nat := 4983230072969 + 3 ^ 40 * 477951 * 2
def baseEnd_477951 : Nat := 245418592297164748214449

theorem tailTrace_477951 : CollatzResearch.WordTrace tailWord_477951 prefixEnd_477951 245418592297164748214449 := by
  unfold tailWord_477951
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432305091472629377209707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11621536727648419584806471 17432305091472629377209707)
  ·
    refine ⟨26148457637208944065814561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432305091472629377209707 26148457637208944065814561)
    ·
      refine ⟨19611343227906708049360921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26148457637208944065814561 19611343227906708049360921)
      ·
        refine ⟨14708507420930031037020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19611343227906708049360921 14708507420930031037020691)
        ·
          refine ⟨22062761131395046555531037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14708507420930031037020691 22062761131395046555531037)
          ·
            refine ⟨8273535424273142458324139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22062761131395046555531037 8273535424273142458324139)
            ·
              refine ⟨12410303136409713687486209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273535424273142458324139 12410303136409713687486209)
              ·
                refine ⟨9307727352307285265614657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12410303136409713687486209 9307727352307285265614657)
                ·
                  refine ⟨6980795514230463949210993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9307727352307285265614657 6980795514230463949210993)
                  ·
                    refine ⟨5235596635672847961908245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980795514230463949210993 5235596635672847961908245)
                    ·
                      refine ⟨245418592297164748214449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5235596635672847961908245 245418592297164748214449)
                      ·
                        rfl

theorem cell23_477951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_477951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477951 prefixEnd_477951 := by exact prefixLift 477951
  have htrace : WordTrace (prefixWord ++ tailWord_477951) baseStart_477951 baseEnd_477951 := by
    simpa [prefixWord, tailWord_477951, baseEnd_477951] using wordTrace_append hprefix tailTrace_477951
  have hstable : (prefixWord ++ tailWord_477951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477951).length < 2 ^ (prefixWord ++ tailWord_477951).sum := by decide
  have hdescent : baseEnd_477951 < baseStart_477951 := by decide
  rcases family_descends (prefixWord ++ tailWord_477951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477959 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_477959 : Nat := 118140960795 + 477959 * 2 ^ 59
def prefixEnd_477959 : Nat := 4983230072969 + 3 ^ 40 * 477959 * 2
def baseEnd_477959 : Nat := 245422700142400716914413

theorem tailTrace_477959 : CollatzResearch.WordTrace tailWord_477959 prefixEnd_477959 245422700142400716914413 := by
  unfold tailWord_477959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432596875443646743500931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11621731250295764495667287 17432596875443646743500931)
  ·
    refine ⟨26148895313165470115251397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432596875443646743500931 26148895313165470115251397)
    ·
      refine ⟨4902917871218525646609637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26148895313165470115251397 4902917871218525646609637)
      ·
        refine ⟨919297100853473558739307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4902917871218525646609637 919297100853473558739307)
        ·
          refine ⟨1378945651280210338108961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919297100853473558739307 1378945651280210338108961)
          ·
            refine ⟨1034209238460157753581721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378945651280210338108961 1034209238460157753581721)
            ·
              refine ⟨775656928845118315186291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034209238460157753581721 775656928845118315186291)
              ·
                refine ⟨1163485393267677472779437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775656928845118315186291 1163485393267677472779437)
                ·
                  refine ⟨436307022475379052292289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1163485393267677472779437 436307022475379052292289)
                  ·
                    refine ⟨327230266856534289219217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436307022475379052292289 327230266856534289219217)
                    ·
                      refine ⟨245422700142400716914413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327230266856534289219217 245422700142400716914413)
                      ·
                        rfl

theorem cell23_477959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_477959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477959 prefixEnd_477959 := by exact prefixLift 477959
  have htrace : WordTrace (prefixWord ++ tailWord_477959) baseStart_477959 baseEnd_477959 := by
    simpa [prefixWord, tailWord_477959, baseEnd_477959] using wordTrace_append hprefix tailTrace_477959
  have hstable : (prefixWord ++ tailWord_477959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477959).length < 2 ^ (prefixWord ++ tailWord_477959).sum := by decide
  have hdescent : baseEnd_477959 < baseStart_477959 := by decide
  rcases family_descends (prefixWord ++ tailWord_477959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_477961 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_477961 : Nat := 118140960795 + 477961 * 2 ^ 59
def prefixEnd_477961 : Nat := 4983230072969 + 3 ^ 40 * 477961 * 2
def baseEnd_477961 : Nat := 81807909034569903029801

theorem tailTrace_477961 : CollatzResearch.WordTrace tailWord_477961 prefixEnd_477961 81807909034569903029801 := by
  unfold tailWord_477961
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432669821436401085073737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11621779880957600723382491 17432669821436401085073737)
  ·
    refine ⟨13074502366077300813805303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17432669821436401085073737 13074502366077300813805303)
    ·
      refine ⟨19611753549115951220707955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074502366077300813805303 19611753549115951220707955)
      ·
        refine ⟨29417630323673926831061933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611753549115951220707955 29417630323673926831061933)
        ·
          refine ⟨11031611371377722561648225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29417630323673926831061933 11031611371377722561648225)
          ·
            refine ⟨8273708528533291921236169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11031611371377722561648225 8273708528533291921236169)
            ·
              refine ⟨6205281396399968940927127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273708528533291921236169 6205281396399968940927127)
              ·
                refine ⟨9307922094599953411390691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205281396399968940927127 9307922094599953411390691)
                ·
                  refine ⟨13961883141899930117086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307922094599953411390691 13961883141899930117086037)
                  ·
                    refine ⟨81807909034569903029801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13961883141899930117086037 81807909034569903029801)
                    ·
                      rfl

theorem cell23_477961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_477961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_477961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_477961 prefixEnd_477961 := by exact prefixLift 477961
  have htrace : WordTrace (prefixWord ++ tailWord_477961) baseStart_477961 baseEnd_477961 := by
    simpa [prefixWord, tailWord_477961, baseEnd_477961] using wordTrace_append hprefix tailTrace_477961
  have hstable : (prefixWord ++ tailWord_477961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_477961).length < 2 ^ (prefixWord ++ tailWord_477961).sum := by decide
  have hdescent : baseEnd_477961 < baseStart_477961 := by decide
  rcases family_descends (prefixWord ++ tailWord_477961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478002 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_478002 : Nat := 118140960795 + 478002 * 2 ^ 59
def prefixEnd_478002 : Nat := 4983230072969 + 3 ^ 40 * 478002 * 2
def baseEnd_478002 : Nat := 245444779810544048676715

theorem tailTrace_478002 : CollatzResearch.WordTrace tailWord_478002 prefixEnd_478002 245444779810544048676715 := by
  unfold tailWord_478002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358541303571966271829065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11622776809525243391544173 4358541303571966271829065)
  ·
    refine ⟨3268905977678974703871799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358541303571966271829065 3268905977678974703871799)
    ·
      refine ⟨4903358966518462055807699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268905977678974703871799 4903358966518462055807699)
      ·
        refine ⟨7355038449777693083711549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903358966518462055807699 7355038449777693083711549)
        ·
          refine ⟨2758139418666634906391831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7355038449777693083711549 2758139418666634906391831)
          ·
            refine ⟨4137209127999952359587747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758139418666634906391831 4137209127999952359587747)
            ·
              refine ⟨6205813691999928539381621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137209127999952359587747 6205813691999928539381621)
              ·
                refine ⟨581795033624993300567027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6205813691999928539381621 581795033624993300567027)
                ·
                  refine ⟨872692550437489950850541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581795033624993300567027 872692550437489950850541)
                  ·
                    refine ⟨327259706414058731568953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872692550437489950850541 327259706414058731568953)
                    ·
                      refine ⟨245444779810544048676715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327259706414058731568953 245444779810544048676715)
                      ·
                        rfl

theorem cell23_478002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_478002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478002 prefixEnd_478002 := by exact prefixLift 478002
  have htrace : WordTrace (prefixWord ++ tailWord_478002) baseStart_478002 baseEnd_478002 := by
    simpa [prefixWord, tailWord_478002, baseEnd_478002] using wordTrace_append hprefix tailTrace_478002
  have hstable : (prefixWord ++ tailWord_478002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478002).length < 2 ^ (prefixWord ++ tailWord_478002).sum := by decide
  have hdescent : baseEnd_478002 < baseStart_478002 := by decide
  rcases family_descends (prefixWord ++ tailWord_478002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478036 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_478036 : Nat := 118140960795 + 478036 * 2 ^ 59
def prefixEnd_478036 : Nat := 4983230072969 + 3 ^ 40 * 478036 * 2
def baseEnd_478036 : Nat := 245462238152796915651559

theorem tailTrace_478036 : CollatzResearch.WordTrace tailWord_478036 prefixEnd_478036 245462238152796915651559 := by
  unfold tailWord_478036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717702648082344447026981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11623603530776459262702641 8717702648082344447026981)
  ·
    refine ⟨1634569246515439583817559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8717702648082344447026981 1634569246515439583817559)
    ·
      refine ⟨2451853869773159375726339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634569246515439583817559 2451853869773159375726339)
      ·
        refine ⟨3677780804659739063589509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451853869773159375726339 3677780804659739063589509)
        ·
          refine ⟨689583900873701074423033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3677780804659739063589509 689583900873701074423033)
          ·
            refine ⟨517187925655275805817275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689583900873701074423033 517187925655275805817275)
            ·
              refine ⟨775781888482913708725913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517187925655275805817275 775781888482913708725913)
              ·
                refine ⟨581836416362185281544435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775781888482913708725913 581836416362185281544435)
                ·
                  refine ⟨872754624543277922316653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581836416362185281544435 872754624543277922316653)
                  ·
                    refine ⟨327282984203729220868745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872754624543277922316653 327282984203729220868745)
                    ·
                      refine ⟨245462238152796915651559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327282984203729220868745 245462238152796915651559)
                      ·
                        rfl

theorem cell23_478036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_478036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478036 prefixEnd_478036 := by exact prefixLift 478036
  have htrace : WordTrace (prefixWord ++ tailWord_478036) baseStart_478036 baseEnd_478036 := by
    simpa [prefixWord, tailWord_478036, baseEnd_478036] using wordTrace_append hprefix tailTrace_478036
  have hstable : (prefixWord ++ tailWord_478036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478036).length < 2 ^ (prefixWord ++ tailWord_478036).sum := by decide
  have hdescent : baseEnd_478036 < baseStart_478036 := by decide
  rcases family_descends (prefixWord ++ tailWord_478036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478075 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 5, 2]
def baseStart_478075 : Nat := 118140960795 + 478075 * 2 ^ 59
def prefixEnd_478075 : Nat := 4983230072969 + 3 ^ 40 * 478075 * 2
def baseEnd_478075 : Nat := 245482263898322263063879

theorem tailTrace_478075 : CollatzResearch.WordTrace tailWord_478075 prefixEnd_478075 245482263898322263063879 := by
  unfold tailWord_478075
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436827743023398554723679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11624551828682265703149119 17436827743023398554723679)
  ·
    refine ⟨26155241614535097832085519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17436827743023398554723679 26155241614535097832085519)
    ·
      refine ⟨39232862421802646748128279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26155241614535097832085519 39232862421802646748128279)
      ·
        refine ⟨58849293632703970122192419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39232862421802646748128279 58849293632703970122192419)
        ·
          refine ⟨88273940449055955183288629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58849293632703970122192419 88273940449055955183288629)
          ·
            refine ⟨8275681917098995798433309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88273940449055955183288629 8275681917098995798433309)
            ·
              refine ⟨3103380718912123424412491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8275681917098995798433309 3103380718912123424412491)
              ·
                refine ⟨4655071078368185136618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103380718912123424412491 4655071078368185136618737)
                ·
                  refine ⟨3491303308776138852464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655071078368185136618737 3491303308776138852464053)
                  ·
                    refine ⟨327309685197763017418505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3491303308776138852464053 327309685197763017418505)
                    ·
                      refine ⟨245482263898322263063879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327309685197763017418505 245482263898322263063879)
                      ·
                        rfl

theorem cell23_478075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5, 2].length) (baseStart_478075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478075 prefixEnd_478075 := by exact prefixLift 478075
  have htrace : WordTrace (prefixWord ++ tailWord_478075) baseStart_478075 baseEnd_478075 := by
    simpa [prefixWord, tailWord_478075, baseEnd_478075] using wordTrace_append hprefix tailTrace_478075
  have hstable : (prefixWord ++ tailWord_478075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478075).length < 2 ^ (prefixWord ++ tailWord_478075).sum := by decide
  have hdescent : baseEnd_478075 < baseStart_478075 := by decide
  rcases family_descends (prefixWord ++ tailWord_478075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478105 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 6, 2]
def baseStart_478105 : Nat := 118140960795 + 478105 * 2 ^ 59
def prefixEnd_478105 : Nat := 4983230072969 + 3 ^ 40 * 478105 * 2
def baseEnd_478105 : Nat := 245497668317957145688741

theorem tailTrace_478105 : CollatzResearch.WordTrace tailWord_478105 prefixEnd_478105 245497668317957145688741 := by
  unfold tailWord_478105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17437921932914713678315769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11625281288609809118877179 17437921932914713678315769)
  ·
    refine ⟨13078441449686035258736827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17437921932914713678315769 13078441449686035258736827)
    ·
      refine ⟨19617662174529052888105241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078441449686035258736827 19617662174529052888105241)
      ·
        refine ⟨14713246630896789666078931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19617662174529052888105241 14713246630896789666078931)
        ·
          refine ⟨22069869946345184499118397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713246630896789666078931 22069869946345184499118397)
          ·
            refine ⟨8276201229879444187169399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22069869946345184499118397 8276201229879444187169399)
            ·
              refine ⟨12414301844819166280754099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276201229879444187169399 12414301844819166280754099)
              ·
                refine ⟨18621452767228749421131149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414301844819166280754099 18621452767228749421131149)
                ·
                  refine ⟨6983044787710781032924181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18621452767228749421131149 6983044787710781032924181)
                  ·
                    refine ⟨327330224423942860918321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6983044787710781032924181 327330224423942860918321)
                    ·
                      refine ⟨245497668317957145688741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327330224423942860918321 245497668317957145688741)
                      ·
                        rfl

theorem cell23_478105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_478105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478105 prefixEnd_478105 := by exact prefixLift 478105
  have htrace : WordTrace (prefixWord ++ tailWord_478105) baseStart_478105 baseEnd_478105 := by
    simpa [prefixWord, tailWord_478105, baseEnd_478105] using wordTrace_append hprefix tailTrace_478105
  have hstable : (prefixWord ++ tailWord_478105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478105).length < 2 ^ (prefixWord ++ tailWord_478105).sum := by decide
  have hdescent : baseEnd_478105 < baseStart_478105 := by decide
  rcases family_descends (prefixWord ++ tailWord_478105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478205 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_478205 : Nat := 118140960795 + 478205 * 2 ^ 59
def prefixEnd_478205 : Nat := 4983230072969 + 3 ^ 40 * 478205 * 2
def baseEnd_478205 : Nat := 81849672127802251479427

theorem tailTrace_478205 : CollatzResearch.WordTrace tailWord_478205 prefixEnd_478205 81849672127802251479427 := by
  unfold tailWord_478205
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441569232552430756956069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11627712821701620504637379 17441569232552430756956069)
  ·
    refine ⟨3270294231103580766929263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17441569232552430756956069 3270294231103580766929263)
    ·
      refine ⟨4905441346655371150393895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270294231103580766929263 4905441346655371150393895)
      ·
        refine ⟨7358162019983056725590843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905441346655371150393895 7358162019983056725590843)
        ·
          refine ⟨11037243029974585088386265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358162019983056725590843 11037243029974585088386265)
          ·
            refine ⟨8277932272480938816289699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037243029974585088386265 8277932272480938816289699)
            ·
              refine ⟨12416898408721408224434549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277932272480938816289699 12416898408721408224434549)
              ·
                refine ⟨1164084225817632021040739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12416898408721408224434549 1164084225817632021040739)
                ·
                  refine ⟨1746126338726448031561109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164084225817632021040739 1746126338726448031561109)
                  ·
                    refine ⟨81849672127802251479427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1746126338726448031561109 81849672127802251479427)
                    ·
                      rfl

theorem cell23_478205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_478205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478205 prefixEnd_478205 := by exact prefixLift 478205
  have htrace : WordTrace (prefixWord ++ tailWord_478205) baseStart_478205 baseEnd_478205 := by
    simpa [prefixWord, tailWord_478205, baseEnd_478205] using wordTrace_append hprefix tailTrace_478205
  have hstable : (prefixWord ++ tailWord_478205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478205).length < 2 ^ (prefixWord ++ tailWord_478205).sum := by decide
  have hdescent : baseEnd_478205 < baseStart_478205 := by decide
  rcases family_descends (prefixWord ++ tailWord_478205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478209 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_478209 : Nat := 118140960795 + 478209 * 2 ^ 59
def prefixEnd_478209 : Nat := 4983230072969 + 3 ^ 40 * 478209 * 2
def baseEnd_478209 : Nat := 81850356768674912929421

theorem tailTrace_478209 : CollatzResearch.WordTrace tailWord_478209 prefixEnd_478209 81850356768674912929421 := by
  unfold tailWord_478209
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441715124537939440101681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11627810083025292960067787 17441715124537939440101681)
  ·
    refine ⟨13081286343403454580076261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441715124537939440101681 13081286343403454580076261)
    ·
      refine ⟨2452741189388147733764299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13081286343403454580076261 2452741189388147733764299)
      ·
        refine ⟨3679111784082221600646449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452741189388147733764299 3679111784082221600646449)
        ·
          refine ⟨2759333838061666200484837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679111784082221600646449 2759333838061666200484837)
          ·
            refine ⟨517375094636562412590907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2759333838061666200484837 517375094636562412590907)
            ·
              refine ⟨776062641954843618886361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517375094636562412590907 776062641954843618886361)
              ·
                refine ⟨582046981466132714164771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776062641954843618886361 582046981466132714164771)
                ·
                  refine ⟨873070472199199071247157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582046981466132714164771 873070472199199071247157)
                  ·
                    refine ⟨81850356768674912929421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 873070472199199071247157 81850356768674912929421)
                    ·
                      rfl

theorem cell23_478209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_478209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478209 prefixEnd_478209 := by exact prefixLift 478209
  have htrace : WordTrace (prefixWord ++ tailWord_478209) baseStart_478209 baseEnd_478209 := by
    simpa [prefixWord, tailWord_478209, baseEnd_478209] using wordTrace_append hprefix tailTrace_478209
  have hstable : (prefixWord ++ tailWord_478209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478209).length < 2 ^ (prefixWord ++ tailWord_478209).sum := by decide
  have hdescent : baseEnd_478209 < baseStart_478209 := by decide
  rcases family_descends (prefixWord ++ tailWord_478209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478222 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_478222 : Nat := 118140960795 + 478222 * 2 ^ 59
def prefixEnd_478222 : Nat := 4983230072969 + 3 ^ 40 * 478222 * 2
def baseEnd_478222 : Nat := 81852581851511062641901

theorem tailTrace_478222 : CollatzResearch.WordTrace tailWord_478222 prefixEnd_478222 81852581851511062641901 := by
  unfold tailWord_478222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180273659186355332540615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11628126182327228440216613 2180273659186355332540615)
  ·
    refine ⟨3270410488779532998810923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180273659186355332540615 3270410488779532998810923)
    ·
      refine ⟨4905615733169299498216385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270410488779532998810923 4905615733169299498216385)
      ·
        refine ⟨3679211799876974623662289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4905615733169299498216385 3679211799876974623662289)
        ·
          refine ⟨2759408849907730967746717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679211799876974623662289 2759408849907730967746717)
          ·
            refine ⟨1034778318715399112905019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2759408849907730967746717 1034778318715399112905019)
            ·
              refine ⟨1552167478073098669357529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034778318715399112905019 1552167478073098669357529)
              ·
                refine ⟨1164125608554824002018147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552167478073098669357529 1164125608554824002018147)
                ·
                  refine ⟨1746188412832236003027221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164125608554824002018147 1746188412832236003027221)
                  ·
                    refine ⟨81852581851511062641901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1746188412832236003027221 81852581851511062641901)
                    ·
                      rfl

theorem cell23_478222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_478222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478222 prefixEnd_478222 := by exact prefixLift 478222
  have htrace : WordTrace (prefixWord ++ tailWord_478222) baseStart_478222 baseEnd_478222 := by
    simpa [prefixWord, tailWord_478222, baseEnd_478222] using wordTrace_append hprefix tailTrace_478222
  have hstable : (prefixWord ++ tailWord_478222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478222).length < 2 ^ (prefixWord ++ tailWord_478222).sum := by decide
  have hdescent : baseEnd_478222 < baseStart_478222 := by decide
  rcases family_descends (prefixWord ++ tailWord_478222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478232 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_478232 : Nat := 118140960795 + 478232 * 2 ^ 59
def prefixEnd_478232 : Nat := 4983230072969 + 3 ^ 40 * 478232 * 2
def baseEnd_478232 : Nat := 245562880361078148800657

theorem tailTrace_478232 : CollatzResearch.WordTrace tailWord_478232 prefixEnd_478232 245562880361078148800657 := by
  unfold tailWord_478232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721277001727307184094475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11628369335636409578792633 8721277001727307184094475)
  ·
    refine ⟨13081915502590960776141713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721277001727307184094475 13081915502590960776141713)
    ·
      refine ⟨9811436626943220582106285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081915502590960776141713 9811436626943220582106285)
      ·
        refine ⟨3679288735103707718289857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9811436626943220582106285 3679288735103707718289857)
        ·
          refine ⟨2759466551327780788717393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679288735103707718289857 2759466551327780788717393)
          ·
            refine ⟨2069599913495835591538045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759466551327780788717393 2069599913495835591538045)
            ·
              refine ⟨776099967560938346826767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2069599913495835591538045 776099967560938346826767)
              ·
                refine ⟨1164149951341407520240151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776099967560938346826767 1164149951341407520240151)
                ·
                  refine ⟨1746224927012111280360227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164149951341407520240151 1746224927012111280360227)
                  ·
                    refine ⟨2619337390518166920540341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746224927012111280360227 2619337390518166920540341)
                    ·
                      refine ⟨245562880361078148800657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2619337390518166920540341 245562880361078148800657)
                      ·
                        rfl

theorem cell23_478232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_478232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478232 prefixEnd_478232 := by exact prefixLift 478232
  have htrace : WordTrace (prefixWord ++ tailWord_478232) baseStart_478232 baseEnd_478232 := by
    simpa [prefixWord, tailWord_478232, baseEnd_478232] using wordTrace_append hprefix tailTrace_478232
  have hstable : (prefixWord ++ tailWord_478232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478232).length < 2 ^ (prefixWord ++ tailWord_478232).sum := by decide
  have hdescent : baseEnd_478232 < baseStart_478232 := by decide
  rcases family_descends (prefixWord ++ tailWord_478232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478239 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 2, 4]
def baseStart_478239 : Nat := 118140960795 + 478239 * 2 ^ 59
def prefixEnd_478239 : Nat := 4983230072969 + 3 ^ 40 * 478239 * 2
def baseEnd_478239 : Nat := 81855491575219873804375

theorem tailTrace_478239 : CollatzResearch.WordTrace tailWord_478239 prefixEnd_478239 81855491575219873804375 := by
  unfold tailWord_478239
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442809314429254563693771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11628539542952836375795847 17442809314429254563693771)
  ·
    refine ⟨26164213971643881845540657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442809314429254563693771 26164213971643881845540657)
    ·
      refine ⟨19623160478732911384155493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26164213971643881845540657 19623160478732911384155493)
      ·
        refine ⟨3679342589762420884529155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19623160478732911384155493 3679342589762420884529155)
        ·
          refine ⟨5519013884643631326793733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679342589762420884529155 5519013884643631326793733)
          ·
            refine ⟨1034815103370680873773825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5519013884643631326793733 1034815103370680873773825)
            ·
              refine ⟨776111327528010655330369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034815103370680873773825 776111327528010655330369)
              ·
                refine ⟨582083495646007991497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776111327528010655330369 582083495646007991497777)
                ·
                  refine ⟨436562621734505993623333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582083495646007991497777 436562621734505993623333)
                  ·
                    refine ⟨81855491575219873804375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436562621734505993623333 81855491575219873804375)
                    ·
                      rfl

theorem cell23_478239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_478239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478239 prefixEnd_478239 := by exact prefixLift 478239
  have htrace : WordTrace (prefixWord ++ tailWord_478239) baseStart_478239 baseEnd_478239 := by
    simpa [prefixWord, tailWord_478239, baseEnd_478239] using wordTrace_append hprefix tailTrace_478239
  have hstable : (prefixWord ++ tailWord_478239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478239).length < 2 ^ (prefixWord ++ tailWord_478239).sum := by decide
  have hdescent : baseEnd_478239 < baseStart_478239 := by decide
  rcases family_descends (prefixWord ++ tailWord_478239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478275 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5]
def baseStart_478275 : Nat := 118140960795 + 478275 * 2 ^ 59
def prefixEnd_478275 : Nat := 4983230072969 + 3 ^ 40 * 478275 * 2
def baseEnd_478275 : Nat := 245584960029221480562959

theorem tailTrace_478275 : CollatzResearch.WordTrace tailWord_478275 prefixEnd_478275 245584960029221480562959 := by
  unfold tailWord_478275
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444122342298832712004279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11629414894865888474669519 17444122342298832712004279)
  ·
    refine ⟨26166183513448249068006419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444122342298832712004279 26166183513448249068006419)
    ·
      refine ⟨39249275270172373602009629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26166183513448249068006419 39249275270172373602009629)
      ·
        refine ⟨14718478226314640100753611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39249275270172373602009629 14718478226314640100753611)
        ·
          refine ⟨22077717339471960151130417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718478226314640100753611 22077717339471960151130417)
          ·
            refine ⟨16558288004603970113347813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22077717339471960151130417 16558288004603970113347813)
            ·
              refine ⟨3104679000863244396252715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16558288004603970113347813 3104679000863244396252715)
              ·
                refine ⟨4657018501294866594379073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104679000863244396252715 4657018501294866594379073)
                ·
                  refine ⟨3492763875971149945784305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657018501294866594379073 3492763875971149945784305)
                  ·
                    refine ⟨2619572906978362459338229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492763875971149945784305 2619572906978362459338229)
                    ·
                      refine ⟨245584960029221480562959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2619572906978362459338229 245584960029221480562959)
                      ·
                        rfl

theorem cell23_478275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_478275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478275 prefixEnd_478275 := by exact prefixLift 478275
  have htrace : WordTrace (prefixWord ++ tailWord_478275) baseStart_478275 baseEnd_478275 := by
    simpa [prefixWord, tailWord_478275, baseEnd_478275] using wordTrace_append hprefix tailTrace_478275
  have hstable : (prefixWord ++ tailWord_478275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478275).length < 2 ^ (prefixWord ++ tailWord_478275).sum := by decide
  have hdescent : baseEnd_478275 < baseStart_478275 := by decide
  rcases family_descends (prefixWord ++ tailWord_478275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478322 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_478322 : Nat := 118140960795 + 478322 * 2 ^ 59
def prefixEnd_478322 : Nat := 4983230072969 + 3 ^ 40 * 478322 * 2
def baseEnd_478322 : Nat := 245609093619982796675243

theorem tailTrace_478322 : CollatzResearch.WordTrace tailWord_478322 prefixEnd_478322 245609093619982796675243 := by
  unfold tailWord_478322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361459143282139934741305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11630557715419039825976813 4361459143282139934741305)
  ·
    refine ⟨3271094357461604951055979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4361459143282139934741305 3271094357461604951055979)
    ·
      refine ⟨4906641536192407426583969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271094357461604951055979 4906641536192407426583969)
      ·
        refine ⟨3679981152144305569937977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4906641536192407426583969 3679981152144305569937977)
        ·
          refine ⟨2759985864108229177453483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679981152144305569937977 2759985864108229177453483)
          ·
            refine ⟨4139978796162343766180225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759985864108229177453483 4139978796162343766180225)
            ·
              refine ⟨3104984097121757824635169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139978796162343766180225 3104984097121757824635169)
              ·
                refine ⟨2328738072841318368476377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104984097121757824635169 2328738072841318368476377)
                ·
                  refine ⟨1746553554630988776357283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328738072841318368476377 1746553554630988776357283)
                  ·
                    refine ⟨2619830331946483164535925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746553554630988776357283 2619830331946483164535925)
                    ·
                      refine ⟨245609093619982796675243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2619830331946483164535925 245609093619982796675243)
                      ·
                        rfl

theorem cell23_478322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_478322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478322 prefixEnd_478322 := by exact prefixLift 478322
  have htrace : WordTrace (prefixWord ++ tailWord_478322) baseStart_478322 baseEnd_478322 := by
    simpa [prefixWord, tailWord_478322, baseEnd_478322] using wordTrace_append hprefix tailTrace_478322
  have hstable : (prefixWord ++ tailWord_478322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478322).length < 2 ^ (prefixWord ++ tailWord_478322).sum := by decide
  have hdescent : baseEnd_478322 < baseStart_478322 := by decide
  rcases family_descends (prefixWord ++ tailWord_478322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478352 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_478352 : Nat := 118140960795 + 478352 * 2 ^ 59
def prefixEnd_478352 : Nat := 4983230072969 + 3 ^ 40 * 478352 * 2
def baseEnd_478352 : Nat := 245624498039617679300105

theorem tailTrace_478352 : CollatzResearch.WordTrace tailWord_478352 prefixEnd_478352 245624498039617679300105 := by
  unfold tailWord_478352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723465381509937431278655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11631287175346583241704873 8723465381509937431278655)
  ·
    refine ⟨13085198072264906146917983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8723465381509937431278655 13085198072264906146917983)
    ·
      refine ⟨19627797108397359220376975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13085198072264906146917983 19627797108397359220376975)
      ·
        refine ⟨29441695662596038830565463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19627797108397359220376975 29441695662596038830565463)
        ·
          refine ⟨44162543493894058245848195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29441695662596038830565463 44162543493894058245848195)
          ·
            refine ⟨66243815240841087368772293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44162543493894058245848195 66243815240841087368772293)
            ·
              refine ⟨12420715357657703881644805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66243815240841087368772293 12420715357657703881644805)
              ·
                refine ⟨2328884129560819477808401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12420715357657703881644805 2328884129560819477808401)
                ·
                  refine ⟨1746663097170614608356301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328884129560819477808401 1746663097170614608356301)
                  ·
                    refine ⟨654998661438980478133613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746663097170614608356301 654998661438980478133613)
                    ·
                      refine ⟨245624498039617679300105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 654998661438980478133613 245624498039617679300105)
                      ·
                        rfl

theorem cell23_478352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_478352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478352 prefixEnd_478352 := by exact prefixLift 478352
  have htrace : WordTrace (prefixWord ++ tailWord_478352) baseStart_478352 baseEnd_478352 := by
    simpa [prefixWord, tailWord_478352, baseEnd_478352] using wordTrace_append hprefix tailTrace_478352
  have hstable : (prefixWord ++ tailWord_478352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478352).length < 2 ^ (prefixWord ++ tailWord_478352).sum := by decide
  have hdescent : baseEnd_478352 < baseStart_478352 := by decide
  rcases family_descends (prefixWord ++ tailWord_478352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478359 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 7]
def baseStart_478359 : Nat := 118140960795 + 478359 * 2 ^ 59
def prefixEnd_478359 : Nat := 4983230072969 + 3 ^ 40 * 478359 * 2
def baseEnd_478359 : Nat := 27292010267133239101397

theorem tailTrace_478359 : CollatzResearch.WordTrace tailWord_478359 prefixEnd_478359 27292010267133239101397 := by
  unfold tailWord_478359
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447186073994515058062131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11631457382663010038708087 17447186073994515058062131)
  ·
    refine ⟨26170779110991772587093197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17447186073994515058062131 26170779110991772587093197)
    ·
      refine ⟨9814042166621914720159949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26170779110991772587093197 9814042166621914720159949)
      ·
        refine ⟨3680265812483218020059981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9814042166621914720159949 3680265812483218020059981)
        ·
          refine ⟨1380099679681206757522493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3680265812483218020059981 1380099679681206757522493)
          ·
            refine ⟨517537379880452534070935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1380099679681206757522493 517537379880452534070935)
            ·
              refine ⟨776306069820678801106403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517537379880452534070935 776306069820678801106403)
              ·
                refine ⟨1164459104731018201659605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776306069820678801106403 1164459104731018201659605)
                ·
                  refine ⟨27292010267133239101397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1164459104731018201659605 27292010267133239101397)
                  ·
                    rfl

theorem cell23_478359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 7].length) (baseStart_478359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478359 prefixEnd_478359 := by exact prefixLift 478359
  have htrace : WordTrace (prefixWord ++ tailWord_478359) baseStart_478359 baseEnd_478359 := by
    simpa [prefixWord, tailWord_478359, baseEnd_478359] using wordTrace_append hprefix tailTrace_478359
  have hstable : (prefixWord ++ tailWord_478359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478359).length < 2 ^ (prefixWord ++ tailWord_478359).sum := by decide
  have hdescent : baseEnd_478359 < baseStart_478359 := by decide
  rcases family_descends (prefixWord ++ tailWord_478359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478370 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_478370 : Nat := 118140960795 + 478370 * 2 ^ 59
def prefixEnd_478370 : Nat := 4983230072969 + 3 ^ 40 * 478370 * 2
def baseEnd_478370 : Nat := 245633740691398608875023

theorem tailTrace_478370 : CollatzResearch.WordTrace tailWord_478370 prefixEnd_478370 245633740691398608875023 := by
  unfold tailWord_478370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361896819238665984178141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11631724851303109291141709 4361896819238665984178141)
  ·
    refine ⟨1635711307214499744066803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4361896819238665984178141 1635711307214499744066803)
    ·
      refine ⟨2453566960821749616100205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635711307214499744066803 2453566960821749616100205)
      ·
        refine ⟨920087610308156106037577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2453566960821749616100205 920087610308156106037577)
        ·
          refine ⟨690065707731117079528183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920087610308156106037577 690065707731117079528183)
          ·
            refine ⟨1035098561596675619292275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690065707731117079528183 1035098561596675619292275)
            ·
              refine ⟨1552647842395013428938413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035098561596675619292275 1552647842395013428938413)
              ·
                refine ⟨582242940898130035851905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552647842395013428938413 582242940898130035851905)
                ·
                  refine ⟨436682205673597526888929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582242940898130035851905 436682205673597526888929)
                  ·
                    refine ⟨327511654255198145166697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436682205673597526888929 327511654255198145166697)
                    ·
                      refine ⟨245633740691398608875023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327511654255198145166697 245633740691398608875023)
                      ·
                        rfl

theorem cell23_478370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_478370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478370 prefixEnd_478370 := by exact prefixLift 478370
  have htrace : WordTrace (prefixWord ++ tailWord_478370) baseStart_478370 baseEnd_478370 := by
    simpa [prefixWord, tailWord_478370, baseEnd_478370] using wordTrace_append hprefix tailTrace_478370
  have hstable : (prefixWord ++ tailWord_478370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478370).length < 2 ^ (prefixWord ++ tailWord_478370).sum := by decide
  have hdescent : baseEnd_478370 < baseStart_478370 := by decide
  rcases family_descends (prefixWord ++ tailWord_478370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478446 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_478446 : Nat := 118140960795 + 478446 * 2 ^ 59
def prefixEnd_478446 : Nat := 4983230072969 + 3 ^ 40 * 478446 * 2
def baseEnd_478446 : Nat := 245672765221140311524673

theorem tailTrace_478446 : CollatzResearch.WordTrace tailWord_478446 prefixEnd_478446 245672765221140311524673 := by
  unfold tailWord_478446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181294903084916114559899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11633572816452885944319461 2181294903084916114559899)
  ·
    refine ⟨3271942354627374171839849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181294903084916114559899 3271942354627374171839849)
    ·
      refine ⟨2453956765970530628879887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271942354627374171839849 2453956765970530628879887)
      ·
        refine ⟨3680935148955795943319831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453956765970530628879887 3680935148955795943319831)
        ·
          refine ⟨5521402723433693914979747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680935148955795943319831 5521402723433693914979747)
          ·
            refine ⟨8282104085150540872469621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521402723433693914979747 8282104085150540872469621)
            ·
              refine ⟨776447257982863206794027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8282104085150540872469621 776447257982863206794027)
              ·
                refine ⟨1164670886974294810191041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776447257982863206794027 1164670886974294810191041)
                ·
                  refine ⟨873503165230721107643281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1164670886974294810191041 873503165230721107643281)
                  ·
                    refine ⟨655127373923040830732461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873503165230721107643281 655127373923040830732461)
                    ·
                      refine ⟨245672765221140311524673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655127373923040830732461 245672765221140311524673)
                      ·
                        rfl

theorem cell23_478446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_478446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478446 prefixEnd_478446 := by exact prefixLift 478446
  have htrace : WordTrace (prefixWord ++ tailWord_478446) baseStart_478446 baseEnd_478446 := by
    simpa [prefixWord, tailWord_478446, baseEnd_478446] using wordTrace_append hprefix tailTrace_478446
  have hstable : (prefixWord ++ tailWord_478446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478446).length < 2 ^ (prefixWord ++ tailWord_478446).sum := by decide
  have hdescent : baseEnd_478446 < baseStart_478446 := by decide
  rcases family_descends (prefixWord ++ tailWord_478446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478466 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_478466 : Nat := 118140960795 + 478466 * 2 ^ 59
def prefixEnd_478466 : Nat := 4983230072969 + 3 ^ 40 * 478466 * 2
def baseEnd_478466 : Nat := 27298114981581137030509

theorem tailTrace_478466 : CollatzResearch.WordTrace tailWord_478466 prefixEnd_478466 27298114981581137030509 := by
  unfold tailWord_478466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362772171151718083051813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11634059123071248221471501 4362772171151718083051813)
  ·
    refine ⟨818019782090947140572215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4362772171151718083051813 818019782090947140572215)
    ·
      refine ⟨1227029673136420710858323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818019782090947140572215 1227029673136420710858323)
      ·
        refine ⟨1840544509704631066287485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227029673136420710858323 1840544509704631066287485)
        ·
          refine ⟨690204191139236649857807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1840544509704631066287485 690204191139236649857807)
          ·
            refine ⟨1035306286708854974786711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690204191139236649857807 1035306286708854974786711)
            ·
              refine ⟨1552959430063282462180067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035306286708854974786711 1552959430063282462180067)
              ·
                refine ⟨2329439145094923693270101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552959430063282462180067 2329439145094923693270101)
                ·
                  refine ⟨27298114981581137030509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2329439145094923693270101 27298114981581137030509)
                  ·
                    rfl

theorem cell23_478466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_478466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478466 prefixEnd_478466 := by exact prefixLift 478466
  have htrace : WordTrace (prefixWord ++ tailWord_478466) baseStart_478466 baseEnd_478466 := by
    simpa [prefixWord, tailWord_478466, baseEnd_478466] using wordTrace_append hprefix tailTrace_478466
  have hstable : (prefixWord ++ tailWord_478466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478466).length < 2 ^ (prefixWord ++ tailWord_478466).sum := by decide
  have hdescent : baseEnd_478466 < baseStart_478466 := by decide
  rcases family_descends (prefixWord ++ tailWord_478466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478476 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_478476 : Nat := 118140960795 + 478476 * 2 ^ 59
def prefixEnd_478476 : Nat := 4983230072969 + 3 ^ 40 * 478476 * 2
def baseEnd_478476 : Nat := 245688169640775194149535

theorem tailTrace_478476 : CollatzResearch.WordTrace tailWord_478476 prefixEnd_478476 245688169640775194149535 := by
  unfold tailWord_478476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725726707285322020035641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11634302276380429360047521 8725726707285322020035641)
  ·
    refine ⟨6544295030463991515026731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8725726707285322020035641 6544295030463991515026731)
    ·
      refine ⟨9816442545695987272540097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544295030463991515026731 9816442545695987272540097)
      ·
        refine ⟨7362331909271990454405073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9816442545695987272540097 7362331909271990454405073)
        ·
          refine ⟨5521748931953992840803805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7362331909271990454405073 5521748931953992840803805)
          ·
            refine ⟨2070655849482747315301427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5521748931953992840803805 2070655849482747315301427)
            ·
              refine ⟨3105983774224120972952141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070655849482747315301427 3105983774224120972952141)
              ·
                refine ⟨1164743915334045364857053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105983774224120972952141 1164743915334045364857053)
                ·
                  refine ⟨436778968250267011821395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164743915334045364857053 436778968250267011821395)
                  ·
                    refine ⟨655168452375400517732093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436778968250267011821395 655168452375400517732093)
                    ·
                      refine ⟨245688169640775194149535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655168452375400517732093 245688169640775194149535)
                      ·
                        rfl

theorem cell23_478476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_478476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478476 prefixEnd_478476 := by exact prefixLift 478476
  have htrace : WordTrace (prefixWord ++ tailWord_478476) baseStart_478476 baseEnd_478476 := by
    simpa [prefixWord, tailWord_478476, baseEnd_478476] using wordTrace_append hprefix tailTrace_478476
  have hstable : (prefixWord ++ tailWord_478476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478476).length < 2 ^ (prefixWord ++ tailWord_478476).sum := by decide
  have hdescent : baseEnd_478476 < baseStart_478476 := by decide
  rcases family_descends (prefixWord ++ tailWord_478476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478493 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_478493 : Nat := 118140960795 + 478493 * 2 ^ 59
def prefixEnd_478493 : Nat := 4983230072969 + 3 ^ 40 * 478493 * 2
def baseEnd_478493 : Nat := 245696898811901627636957

theorem tailTrace_478493 : CollatzResearch.WordTrace tailWord_478493 prefixEnd_478493 245696898811901627636957 := by
  unfold tailWord_478493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17452073455509055943440133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11634715637006037295626755 17452073455509055943440133)
  ·
    refine ⟨3272263772907947989395025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17452073455509055943440133 3272263772907947989395025)
    ·
      refine ⟨2454197829680960992046269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272263772907947989395025 2454197829680960992046269)
      ·
        refine ⟨920324186130360372017351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454197829680960992046269 920324186130360372017351)
        ·
          refine ⟨1380486279195540558026027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920324186130360372017351 1380486279195540558026027)
          ·
            refine ⟨2070729418793310837039041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380486279195540558026027 2070729418793310837039041)
            ·
              refine ⟨1553047064094983127779281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070729418793310837039041 1553047064094983127779281)
              ·
                refine ⟨1164785298071237345834461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553047064094983127779281 1164785298071237345834461)
                ·
                  refine ⟨436794486776714004687923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164785298071237345834461 436794486776714004687923)
                  ·
                    refine ⟨655191730165071007031885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436794486776714004687923 655191730165071007031885)
                    ·
                      refine ⟨245696898811901627636957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655191730165071007031885 245696898811901627636957)
                      ·
                        rfl

theorem cell23_478493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_478493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478493 prefixEnd_478493 := by exact prefixLift 478493
  have htrace : WordTrace (prefixWord ++ tailWord_478493) baseStart_478493 baseEnd_478493 := by
    simpa [prefixWord, tailWord_478493, baseEnd_478493] using wordTrace_append hprefix tailTrace_478493
  have hstable : (prefixWord ++ tailWord_478493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478493).length < 2 ^ (prefixWord ++ tailWord_478493).sum := by decide
  have hdescent : baseEnd_478493 < baseStart_478493 := by decide
  rcases family_descends (prefixWord ++ tailWord_478493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478519 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_478519 : Nat := 118140960795 + 478519 * 2 ^ 59
def prefixEnd_478519 : Nat := 4983230072969 + 3 ^ 40 * 478519 * 2
def baseEnd_478519 : Nat := 245710249308918525911837

theorem tailTrace_478519 : CollatzResearch.WordTrace tailWord_478519 prefixEnd_478519 245710249308918525911837 := by
  unfold tailWord_478519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453021753414862383886611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11635347835609908255924407 17453021753414862383886611)
  ·
    refine ⟨26179532630122293575829917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17453021753414862383886611 26179532630122293575829917)
    ·
      refine ⟨9817324736295860090936219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26179532630122293575829917 9817324736295860090936219)
      ·
        refine ⟨14725987104443790136404329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817324736295860090936219 14725987104443790136404329)
        ·
          refine ⟨11044490328332842602303247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14725987104443790136404329 11044490328332842602303247)
          ·
            refine ⟨16566735492499263903454871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044490328332842602303247 16566735492499263903454871)
            ·
              refine ⟨24850103238748895855182307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16566735492499263903454871 24850103238748895855182307)
              ·
                refine ⟨37275154858123343782773461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24850103238748895855182307 37275154858123343782773461)
                ·
                  refine ⟨873636441987265869908753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37275154858123343782773461 873636441987265869908753)
                  ·
                    refine ⟨655227331490449402431565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873636441987265869908753 655227331490449402431565)
                    ·
                      refine ⟨245710249308918525911837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655227331490449402431565 245710249308918525911837)
                      ·
                        rfl

theorem cell23_478519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_478519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478519 prefixEnd_478519 := by exact prefixLift 478519
  have htrace : WordTrace (prefixWord ++ tailWord_478519) baseStart_478519 baseEnd_478519 := by
    simpa [prefixWord, tailWord_478519, baseEnd_478519] using wordTrace_append hprefix tailTrace_478519
  have hstable : (prefixWord ++ tailWord_478519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478519).length < 2 ^ (prefixWord ++ tailWord_478519).sum := by decide
  have hdescent : baseEnd_478519 < baseStart_478519 := by decide
  rcases family_descends (prefixWord ++ tailWord_478519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478526 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_478526 : Nat := 118140960795 + 478526 * 2 ^ 59
def prefixEnd_478526 : Nat := 4983230072969 + 3 ^ 40 * 478526 * 2
def baseEnd_478526 : Nat := 81904614557833332841435

theorem tailTrace_478526 : CollatzResearch.WordTrace tailWord_478526 prefixEnd_478526 81904614557833332841435 := by
  unfold tailWord_478526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181659633048687822423929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11635518042926335052927621 2181659633048687822423929)
  ·
    refine ⟨1636244724786515866817947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181659633048687822423929 1636244724786515866817947)
    ·
      refine ⟨2454367087179773800226921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636244724786515866817947 2454367087179773800226921)
      ·
        refine ⟨1840775315384830350170191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454367087179773800226921 1840775315384830350170191)
        ·
          refine ⟨2761162973077245525255287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840775315384830350170191 2761162973077245525255287)
          ·
            refine ⟨4141744459615868287882931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761162973077245525255287 4141744459615868287882931)
            ·
              refine ⟨6212616689423802431824397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141744459615868287882931 6212616689423802431824397)
              ·
                refine ⟨2329731258533925911934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6212616689423802431824397 2329731258533925911934149)
                ·
                  refine ⟨436824610975111108487653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329731258533925911934149 436824610975111108487653)
                  ·
                    refine ⟨81904614557833332841435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436824610975111108487653 81904614557833332841435)
                    ·
                      rfl

theorem cell23_478526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_478526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478526 prefixEnd_478526 := by exact prefixLift 478526
  have htrace : WordTrace (prefixWord ++ tailWord_478526) baseStart_478526 baseEnd_478526 := by
    simpa [prefixWord, tailWord_478526, baseEnd_478526] using wordTrace_append hprefix tailTrace_478526
  have hstable : (prefixWord ++ tailWord_478526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478526).length < 2 ^ (prefixWord ++ tailWord_478526).sum := by decide
  have hdescent : baseEnd_478526 < baseStart_478526 := by decide
  rcases family_descends (prefixWord ++ tailWord_478526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478534 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_478534 : Nat := 118140960795 + 478534 * 2 ^ 59
def prefixEnd_478534 : Nat := 4983230072969 + 3 ^ 40 * 478534 * 2
def baseEnd_478534 : Nat := 27301994613192885247141

theorem tailTrace_478534 : CollatzResearch.WordTrace tailWord_478534 prefixEnd_478534 27301994613192885247141 := by
  unfold tailWord_478534
  simp only [CollatzResearch.WordTrace]
  refine ⟨545424026511266248302583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11635712565573679963788437 545424026511266248302583)
  ·
    refine ⟨818136039766899372453875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545424026511266248302583 818136039766899372453875)
    ·
      refine ⟨1227204059650349058680813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818136039766899372453875 1227204059650349058680813)
      ·
        refine ⟨460201522368880897005305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1227204059650349058680813 460201522368880897005305)
        ·
          refine ⟨345151141776660672753979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460201522368880897005305 345151141776660672753979)
          ·
            refine ⟨517726712664991009130969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345151141776660672753979 517726712664991009130969)
            ·
              refine ⟨388295034498743256848227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517726712664991009130969 388295034498743256848227)
              ·
                refine ⟨582442551748114885272341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388295034498743256848227 582442551748114885272341)
                ·
                  refine ⟨27301994613192885247141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 582442551748114885272341 27301994613192885247141)
                  ·
                    rfl

theorem cell23_478534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_478534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478534 prefixEnd_478534 := by exact prefixLift 478534
  have htrace : WordTrace (prefixWord ++ tailWord_478534) baseStart_478534 baseEnd_478534 := by
    simpa [prefixWord, tailWord_478534, baseEnd_478534] using wordTrace_append hprefix tailTrace_478534
  have hstable : (prefixWord ++ tailWord_478534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478534).length < 2 ^ (prefixWord ++ tailWord_478534).sum := by decide
  have hdescent : baseEnd_478534 < baseStart_478534 := by decide
  rcases family_descends (prefixWord ++ tailWord_478534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478570 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_478570 : Nat := 118140960795 + 478570 * 2 ^ 59
def prefixEnd_478570 : Nat := 4983230072969 + 3 ^ 40 * 478570 * 2
def baseEnd_478570 : Nat := 245736436822297826374103

theorem tailTrace_478570 : CollatzResearch.WordTrace tailWord_478570 prefixEnd_478570 245736436822297826374103 := by
  unfold tailWord_478570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363720469057524523498291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11636587917486732062662109 4363720469057524523498291)
  ·
    refine ⟨6545580703586286785247437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4363720469057524523498291 6545580703586286785247437)
    ·
      refine ⟨2454592763844857544467789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6545580703586286785247437 2454592763844857544467789)
      ·
        refine ⟨920472286441821579175421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454592763844857544467789 920472286441821579175421)
        ·
          refine ⟨345177107415683092190783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920472286441821579175421 345177107415683092190783)
          ·
            refine ⟨517765661123524638286175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345177107415683092190783 517765661123524638286175)
            ·
              refine ⟨776648491685286957429263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517765661123524638286175 776648491685286957429263)
              ·
                refine ⟨1164972737527930436143895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776648491685286957429263 1164972737527930436143895)
                ·
                  refine ⟨1747459106291895654215843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164972737527930436143895 1747459106291895654215843)
                  ·
                    refine ⟨2621188659437843481323765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1747459106291895654215843 2621188659437843481323765)
                    ·
                      refine ⟨245736436822297826374103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2621188659437843481323765 245736436822297826374103)
                      ·
                        rfl

theorem cell23_478570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_478570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478570 prefixEnd_478570 := by exact prefixLift 478570
  have htrace : WordTrace (prefixWord ++ tailWord_478570) baseStart_478570 baseEnd_478570 := by
    simpa [prefixWord, tailWord_478570, baseEnd_478570] using wordTrace_append hprefix tailTrace_478570
  have hstable : (prefixWord ++ tailWord_478570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478570).length < 2 ^ (prefixWord ++ tailWord_478570).sum := by decide
  have hdescent : baseEnd_478570 < baseStart_478570 := by decide
  rcases family_descends (prefixWord ++ tailWord_478570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478583 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_478583 : Nat := 118140960795 + 478583 * 2 ^ 59
def prefixEnd_478583 : Nat := 4983230072969 + 3 ^ 40 * 478583 * 2
def baseEnd_478583 : Nat := 245743112070806275511543

theorem tailTrace_478583 : CollatzResearch.WordTrace tailWord_478583 prefixEnd_478583 245743112070806275511543 := by
  unfold tailWord_478583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455356025183001314216403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11636904016788667542810935 17455356025183001314216403)
  ·
    refine ⟨26183034037774501971324605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455356025183001314216403 26183034037774501971324605)
    ·
      refine ⟨9818637764165438239246727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26183034037774501971324605 9818637764165438239246727)
      ·
        refine ⟨14727956646248157358870091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818637764165438239246727 14727956646248157358870091)
        ·
          refine ⟨22091934969372236038305137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727956646248157358870091 22091934969372236038305137)
          ·
            refine ⟨16568951227029177028728853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22091934969372236038305137 16568951227029177028728853)
            ·
              refine ⟨776669588766992673221665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16568951227029177028728853 776669588766992673221665)
              ·
                refine ⟨582502191575244504916249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776669588766992673221665 582502191575244504916249)
                ·
                  refine ⟨436876643681433378687187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582502191575244504916249 436876643681433378687187)
                  ·
                    refine ⟨655314965522150068030781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436876643681433378687187 655314965522150068030781)
                    ·
                      refine ⟨245743112070806275511543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655314965522150068030781 245743112070806275511543)
                      ·
                        rfl

theorem cell23_478583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_478583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478583 prefixEnd_478583 := by exact prefixLift 478583
  have htrace : WordTrace (prefixWord ++ tailWord_478583) baseStart_478583 baseEnd_478583 := by
    simpa [prefixWord, tailWord_478583, baseEnd_478583] using wordTrace_append hprefix tailTrace_478583
  have hstable : (prefixWord ++ tailWord_478583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478583).length < 2 ^ (prefixWord ++ tailWord_478583).sum := by decide
  have hdescent : baseEnd_478583 < baseStart_478583 := by decide
  rcases family_descends (prefixWord ++ tailWord_478583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478589 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_478589 : Nat := 118140960795 + 478589 * 2 ^ 59
def prefixEnd_478589 : Nat := 4983230072969 + 3 ^ 40 * 478589 * 2
def baseEnd_478589 : Nat := 245746192954733252036515

theorem tailTrace_478589 : CollatzResearch.WordTrace tailWord_478589 prefixEnd_478589 245746192954733252036515 := by
  unfold tailWord_478589
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455574863161264338934821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637049908774176225956547 17455574863161264338934821)
  ·
    refine ⟨3272920286842737063550279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17455574863161264338934821 3272920286842737063550279)
    ·
      refine ⟨4909380430264105595325419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272920286842737063550279 4909380430264105595325419)
      ·
        refine ⟨7364070645396158392988129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909380430264105595325419 7364070645396158392988129)
        ·
          refine ⟨5523052984047118794741097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364070645396158392988129 5523052984047118794741097)
          ·
            refine ⟨4142289738035339096055823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523052984047118794741097 4142289738035339096055823)
            ·
              refine ⟨6213434607053008644083735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142289738035339096055823 6213434607053008644083735)
              ·
                refine ⟨9320151910579512966125603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213434607053008644083735 9320151910579512966125603)
                ·
                  refine ⟨13980227865869269449188405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320151910579512966125603 13980227865869269449188405)
                  ·
                    refine ⟨1310646362425244010861413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13980227865869269449188405 1310646362425244010861413)
                    ·
                      refine ⟨245746192954733252036515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1310646362425244010861413 245746192954733252036515)
                      ·
                        rfl

theorem cell23_478589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_478589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478589 prefixEnd_478589 := by exact prefixLift 478589
  have htrace : WordTrace (prefixWord ++ tailWord_478589) baseStart_478589 baseEnd_478589 := by
    simpa [prefixWord, tailWord_478589, baseEnd_478589] using wordTrace_append hprefix tailTrace_478589
  have hstable : (prefixWord ++ tailWord_478589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478589).length < 2 ^ (prefixWord ++ tailWord_478589).sum := by decide
  have hdescent : baseEnd_478589 < baseStart_478589 := by decide
  rcases family_descends (prefixWord ++ tailWord_478589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478590 : List Nat := [4, 2, 3, 2, 1, 2, 1, 8]
def baseStart_478590 : Nat := 118140960795 + 478590 * 2 ^ 59
def prefixEnd_478590 : Nat := 4983230072969 + 3 ^ 40 * 478590 * 2
def baseEnd_478590 : Nat := 9101729867977324004593

theorem tailTrace_478590 : CollatzResearch.WordTrace tailWord_478590 prefixEnd_478590 9101729867977324004593 := by
  unfold tailWord_478590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181951417019705188715153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11637074224105094339814149 2181951417019705188715153)
  ·
    refine ⟨1636463562764778891536365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181951417019705188715153 1636463562764778891536365)
    ·
      refine ⟨613673836036792084326137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1636463562764778891536365 613673836036792084326137)
      ·
        refine ⟨460255377027594063244603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613673836036792084326137 460255377027594063244603)
        ·
          refine ⟨690383065541391094866905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460255377027594063244603 690383065541391094866905)
          ·
            refine ⟨517787299156043321150179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690383065541391094866905 517787299156043321150179)
            ·
              refine ⟨776680948734064981725269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517787299156043321150179 776680948734064981725269)
              ·
                refine ⟨9101729867977324004593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 776680948734064981725269 9101729867977324004593)
                ·
                  rfl

theorem cell23_478590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_478590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478590 prefixEnd_478590 := by exact prefixLift 478590
  have htrace : WordTrace (prefixWord ++ tailWord_478590) baseStart_478590 baseEnd_478590 := by
    simpa [prefixWord, tailWord_478590, baseEnd_478590] using wordTrace_append hprefix tailTrace_478590
  have hstable : (prefixWord ++ tailWord_478590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478590).length < 2 ^ (prefixWord ++ tailWord_478590).sum := by decide
  have hdescent : baseEnd_478590 < baseStart_478590 := by decide
  rcases family_descends (prefixWord ++ tailWord_478590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478599 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 8]
def baseStart_478599 : Nat := 118140960795 + 478599 * 2 ^ 59
def prefixEnd_478599 : Nat := 4983230072969 + 3 ^ 40 * 478599 * 2
def baseEnd_478599 : Nat := 81917109253759404303823

theorem tailTrace_478599 : CollatzResearch.WordTrace tailWord_478599 prefixEnd_478599 81917109253759404303823 := by
  unfold tailWord_478599
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455939593125036046798851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637293062083357364532567 17455939593125036046798851)
  ·
    refine ⟨26183909389687554070198277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455939593125036046798851 26183909389687554070198277)
    ·
      refine ⟨4909483010566416388162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26183909389687554070198277 4909483010566416388162177)
      ·
        refine ⟨3682112257924812291121633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4909483010566416388162177 3682112257924812291121633)
        ·
          refine ⟨2761584193443609218341225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682112257924812291121633 2761584193443609218341225)
          ·
            refine ⟨2071188145082706913755919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761584193443609218341225 2071188145082706913755919)
            ·
              refine ⟨3106782217624060370633879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071188145082706913755919 3106782217624060370633879)
              ·
                refine ⟨4660173326436090555950819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106782217624060370633879 4660173326436090555950819)
                ·
                  refine ⟨6990259989654135833926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660173326436090555950819 6990259989654135833926229)
                  ·
                    refine ⟨81917109253759404303823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6990259989654135833926229 81917109253759404303823)
                    ·
                      rfl

theorem cell23_478599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_478599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478599 prefixEnd_478599 := by exact prefixLift 478599
  have htrace : WordTrace (prefixWord ++ tailWord_478599) baseStart_478599 baseEnd_478599 := by
    simpa [prefixWord, tailWord_478599, baseEnd_478599] using wordTrace_append hprefix tailTrace_478599
  have hstable : (prefixWord ++ tailWord_478599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478599).length < 2 ^ (prefixWord ++ tailWord_478599).sum := by decide
  have hdescent : baseEnd_478599 < baseStart_478599 := by decide
  rcases family_descends (prefixWord ++ tailWord_478599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478623 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 4, 2]
def baseStart_478623 : Nat := 118140960795 + 478623 * 2 ^ 59
def prefixEnd_478623 : Nat := 4983230072969 + 3 ^ 40 * 478623 * 2
def baseEnd_478623 : Nat := 245763651296986119011359

theorem tailTrace_478623 : CollatzResearch.WordTrace tailWord_478623 prefixEnd_478623 245763651296986119011359 := by
  unfold tailWord_478623
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456814945038088145672523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11637876630025392097115015 17456814945038088145672523)
  ·
    refine ⟨26185222417557132218508785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17456814945038088145672523 26185222417557132218508785)
    ·
      refine ⟨19638916813167849163881589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26185222417557132218508785 19638916813167849163881589)
      ·
        refine ⟨1841148451234485859113899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19638916813167849163881589 1841148451234485859113899)
        ·
          refine ⟨2761722676851728788670849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841148451234485859113899 2761722676851728788670849)
          ·
            refine ⟨2071292007638796591503137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761722676851728788670849 2071292007638796591503137)
            ·
              refine ⟨1553469005729097443627353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071292007638796591503137 1553469005729097443627353)
              ·
                refine ⟨1165101754296823082720515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553469005729097443627353 1165101754296823082720515)
                ·
                  refine ⟨1747652631445234624080773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165101754296823082720515 1747652631445234624080773)
                  ·
                    refine ⟨327684868395981492015145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747652631445234624080773 327684868395981492015145)
                    ·
                      refine ⟨245763651296986119011359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327684868395981492015145 245763651296986119011359)
                      ·
                        rfl

theorem cell23_478623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_478623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478623 prefixEnd_478623 := by exact prefixLift 478623
  have htrace : WordTrace (prefixWord ++ tailWord_478623) baseStart_478623 baseEnd_478623 := by
    simpa [prefixWord, tailWord_478623, baseEnd_478623] using wordTrace_append hprefix tailTrace_478623
  have hstable : (prefixWord ++ tailWord_478623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478623).length < 2 ^ (prefixWord ++ tailWord_478623).sum := by decide
  have hdescent : baseEnd_478623 < baseStart_478623 := by decide
  rcases family_descends (prefixWord ++ tailWord_478623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478656 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_478656 : Nat := 118140960795 + 478656 * 2 ^ 59
def prefixEnd_478656 : Nat := 4983230072969 + 3 ^ 40 * 478656 * 2
def baseEnd_478656 : Nat := 245780596158584489898707

theorem tailTrace_478656 : CollatzResearch.WordTrace tailWord_478656 prefixEnd_478656 245780596158584489898707 := by
  unfold tailWord_478656
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729009276959267390811911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11638679035945689854415881 8729009276959267390811911)
  ·
    refine ⟨13093513915438901086217867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729009276959267390811911 13093513915438901086217867)
    ·
      refine ⟨19640270873158351629326801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093513915438901086217867 19640270873158351629326801)
      ·
        refine ⟨14730203154868763721995101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19640270873158351629326801 14730203154868763721995101)
        ·
          refine ⟨5523826183075786395748163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14730203154868763721995101 5523826183075786395748163)
          ·
            refine ⟨8285739274613679593622245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523826183075786395748163 8285739274613679593622245)
            ·
              refine ⟨1553576113990064923804171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8285739274613679593622245 1553576113990064923804171)
              ·
                refine ⟨2330364170985097385706257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553576113990064923804171 2330364170985097385706257)
                ·
                  refine ⟨1747773128238823039279693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330364170985097385706257 1747773128238823039279693)
                  ·
                    refine ⟨655414923089558639729885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747773128238823039279693 655414923089558639729885)
                    ·
                      refine ⟨245780596158584489898707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655414923089558639729885 245780596158584489898707)
                      ·
                        rfl

theorem cell23_478656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_478656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478656 prefixEnd_478656 := by exact prefixLift 478656
  have htrace : WordTrace (prefixWord ++ tailWord_478656) baseStart_478656 baseEnd_478656 := by
    simpa [prefixWord, tailWord_478656, baseEnd_478656] using wordTrace_append hprefix tailTrace_478656
  have hstable : (prefixWord ++ tailWord_478656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478656).length < 2 ^ (prefixWord ++ tailWord_478656).sum := by decide
  have hdescent : baseEnd_478656 < baseStart_478656 := by decide
  rcases family_descends (prefixWord ++ tailWord_478656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478659 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 7]
def baseStart_478659 : Nat := 118140960795 + 478659 * 2 ^ 59
def prefixEnd_478659 : Nat := 4983230072969 + 3 ^ 40 * 478659 * 2
def baseEnd_478659 : Nat := 81927378866849326053731

theorem tailTrace_478659 : CollatzResearch.WordTrace tailWord_478659 prefixEnd_478659 81927378866849326053731 := by
  unfold tailWord_478659
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458127972907666293983031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11638751981938444195988687 17458127972907666293983031)
  ·
    refine ⟨26187191959361499440974547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458127972907666293983031 26187191959361499440974547)
    ·
      refine ⟨39280787939042249161461821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187191959361499440974547 39280787939042249161461821)
      ·
        refine ⟨14730295477140843435548183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39280787939042249161461821 14730295477140843435548183)
        ·
          refine ⟨22095443215711265153322275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730295477140843435548183 22095443215711265153322275)
          ·
            refine ⟨33143164823566897729983413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22095443215711265153322275 33143164823566897729983413)
            ·
              refine ⟨3107171702209396662185945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33143164823566897729983413 3107171702209396662185945)
              ·
                refine ⟨2330378776657047496639459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107171702209396662185945 2330378776657047496639459)
                ·
                  refine ⟨3495568164985571244959189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330378776657047496639459 3495568164985571244959189)
                  ·
                    refine ⟨81927378866849326053731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3495568164985571244959189 81927378866849326053731)
                    ·
                      rfl

theorem cell23_478659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 7].length) (baseStart_478659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478659 prefixEnd_478659 := by exact prefixLift 478659
  have htrace : WordTrace (prefixWord ++ tailWord_478659) baseStart_478659 baseEnd_478659 := by
    simpa [prefixWord, tailWord_478659, baseEnd_478659] using wordTrace_append hprefix tailTrace_478659
  have hstable : (prefixWord ++ tailWord_478659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478659).length < 2 ^ (prefixWord ++ tailWord_478659).sum := by decide
  have hdescent : baseEnd_478659 < baseStart_478659 := by decide
  rcases family_descends (prefixWord ++ tailWord_478659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478693 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_478693 : Nat := 118140960795 + 478693 * 2 ^ 59
def prefixEnd_478693 : Nat := 4983230072969 + 3 ^ 40 * 478693 * 2
def baseEnd_478693 : Nat := 81933198314266948378679

theorem tailTrace_478693 : CollatzResearch.WordTrace tailWord_478693 prefixEnd_478693 81933198314266948378679 := by
  unfold tailWord_478693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459368054784490100720733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11639578703189660067147155 17459368054784490100720733)
  ·
    refine ⟨6547263020544183787770275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17459368054784490100720733 6547263020544183787770275)
    ·
      refine ⟨9820894530816275681655413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547263020544183787770275 9820894530816275681655413)
      ·
        refine ⟨920708862264025845155195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9820894530816275681655413 920708862264025845155195)
        ·
          refine ⟨1381063293396038767732793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920708862264025845155195 1381063293396038767732793)
          ·
            refine ⟨1035797470047029075799595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381063293396038767732793 1035797470047029075799595)
            ·
              refine ⟨1553696205070543613699393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035797470047029075799595 1553696205070543613699393)
              ·
                refine ⟨1165272153802907710274545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553696205070543613699393 1165272153802907710274545)
                ·
                  refine ⟨873954115352180782705909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165272153802907710274545 873954115352180782705909)
                  ·
                    refine ⟨81933198314266948378679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 873954115352180782705909 81933198314266948378679)
                    ·
                      rfl

theorem cell23_478693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_478693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478693 prefixEnd_478693 := by exact prefixLift 478693
  have htrace : WordTrace (prefixWord ++ tailWord_478693) baseStart_478693 baseEnd_478693 := by
    simpa [prefixWord, tailWord_478693, baseEnd_478693] using wordTrace_append hprefix tailTrace_478693
  have hstable : (prefixWord ++ tailWord_478693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478693).length < 2 ^ (prefixWord ++ tailWord_478693).sum := by decide
  have hdescent : baseEnd_478693 < baseStart_478693 := by decide
  rcases family_descends (prefixWord ++ tailWord_478693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478699 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5]
def baseStart_478699 : Nat := 118140960795 + 478699 * 2 ^ 59
def prefixEnd_478699 : Nat := 4983230072969 + 3 ^ 40 * 478699 * 2
def baseEnd_478699 : Nat := 245802675826727821661009

theorem tailTrace_478699 : CollatzResearch.WordTrace tailWord_478699 prefixEnd_478699 245802675826727821661009 := by
  unfold tailWord_478699
  simp only [CollatzResearch.WordTrace]
  refine ⟨17459586892762753125439151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11639724595175168750292767 17459586892762753125439151)
  ·
    refine ⟨26189380339144129688158727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17459586892762753125439151 26189380339144129688158727)
    ·
      refine ⟨39284070508716194532238091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26189380339144129688158727 39284070508716194532238091)
      ·
        refine ⟨58926105763074291798357137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39284070508716194532238091 58926105763074291798357137)
        ·
          refine ⟨44194579322305718848767853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58926105763074291798357137 44194579322305718848767853)
          ·
            refine ⟨16572967245864644568287945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44194579322305718848767853 16572967245864644568287945)
            ·
              refine ⟨12429725434398483426215959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16572967245864644568287945 12429725434398483426215959)
              ·
                refine ⟨18644588151597725139323939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429725434398483426215959 18644588151597725139323939)
                ·
                  refine ⟨27966882227396587708985909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18644588151597725139323939 27966882227396587708985909)
                  ·
                    refine ⟨2621895208818430097717429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27966882227396587708985909 2621895208818430097717429)
                    ·
                      refine ⟨245802675826727821661009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2621895208818430097717429 245802675826727821661009)
                      ·
                        rfl

theorem cell23_478699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_478699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478699 prefixEnd_478699 := by exact prefixLift 478699
  have htrace : WordTrace (prefixWord ++ tailWord_478699) baseStart_478699 baseEnd_478699 := by
    simpa [prefixWord, tailWord_478699, baseEnd_478699] using wordTrace_append hprefix tailTrace_478699
  have hstable : (prefixWord ++ tailWord_478699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478699).length < 2 ^ (prefixWord ++ tailWord_478699).sum := by decide
  have hdescent : baseEnd_478699 < baseStart_478699 := by decide
  rcases family_descends (prefixWord ++ tailWord_478699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478716 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_478716 : Nat := 118140960795 + 478716 * 2 ^ 59
def prefixEnd_478716 : Nat := 4983230072969 + 3 ^ 40 * 478716 * 2
def baseEnd_478716 : Nat := 245811404997854255148431

theorem tailTrace_478716 : CollatzResearch.WordTrace tailWord_478716 prefixEnd_478716 245811404997854255148431 := by
  unfold tailWord_478716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730103466850582514404001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11640137955800776685872001 8730103466850582514404001)
  ·
    refine ⟨6547577600137936885803001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8730103466850582514404001 6547577600137936885803001)
    ·
      refine ⟨4910683200103452664352251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6547577600137936885803001 4910683200103452664352251)
      ·
        refine ⟨7366024800155178996528377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4910683200103452664352251 7366024800155178996528377)
        ·
          refine ⟨5524518600116384247396283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7366024800155178996528377 5524518600116384247396283)
          ·
            refine ⟨8286777900174576371094425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524518600116384247396283 8286777900174576371094425)
            ·
              refine ⟨6215083425130932278320819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286777900174576371094425 6215083425130932278320819)
              ·
                refine ⟨9322625137696398417481229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215083425130932278320819 9322625137696398417481229)
                ·
                  refine ⟨3495984426636149406555461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9322625137696398417481229 3495984426636149406555461)
                  ·
                    refine ⟨655497079994278013729149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495984426636149406555461 655497079994278013729149)
                    ·
                      refine ⟨245811404997854255148431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655497079994278013729149 245811404997854255148431)
                      ·
                        rfl

theorem cell23_478716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_478716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478716 prefixEnd_478716 := by exact prefixLift 478716
  have htrace : WordTrace (prefixWord ++ tailWord_478716) baseStart_478716 baseEnd_478716 := by
    simpa [prefixWord, tailWord_478716, baseEnd_478716] using wordTrace_append hprefix tailTrace_478716
  have hstable : (prefixWord ++ tailWord_478716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478716).length < 2 ^ (prefixWord ++ tailWord_478716).sum := by decide
  have hdescent : baseEnd_478716 < baseStart_478716 := by decide
  rcases family_descends (prefixWord ++ tailWord_478716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478719 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 10]
def baseStart_478719 : Nat := 118140960795 + 478719 * 2 ^ 59
def prefixEnd_478719 : Nat := 4983230072969 + 3 ^ 40 * 478719 * 2
def baseEnd_478719 : Nat := 27312549493313082601213

theorem tailTrace_478719 : CollatzResearch.WordTrace tailWord_478719 prefixEnd_478719 27312549493313082601213 := by
  unfold tailWord_478719
  simp only [CollatzResearch.WordTrace]
  refine ⟨17460316352690296541167211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11640210901793531027444807 17460316352690296541167211)
  ·
    refine ⟨26190474529035444811750817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17460316352690296541167211 26190474529035444811750817)
    ·
      refine ⟨19642855896776583608813113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26190474529035444811750817 19642855896776583608813113)
      ·
        refine ⟨14732141922582437706609835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19642855896776583608813113 14732141922582437706609835)
        ·
          refine ⟨22098212883873656559914753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732141922582437706609835 22098212883873656559914753)
          ·
            refine ⟨16573659662905242419936065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22098212883873656559914753 16573659662905242419936065)
            ·
              refine ⟨12430244747178931814952049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16573659662905242419936065 12430244747178931814952049)
              ·
                refine ⟨9322683560384198861214037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12430244747178931814952049 9322683560384198861214037)
                ·
                  refine ⟨27312549493313082601213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9322683560384198861214037 27312549493313082601213)
                  ·
                    rfl

theorem cell23_478719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 10].length) (baseStart_478719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478719 prefixEnd_478719 := by exact prefixLift 478719
  have htrace : WordTrace (prefixWord ++ tailWord_478719) baseStart_478719 baseEnd_478719 := by
    simpa [prefixWord, tailWord_478719, baseEnd_478719] using wordTrace_append hprefix tailTrace_478719
  have hstable : (prefixWord ++ tailWord_478719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478719).length < 2 ^ (prefixWord ++ tailWord_478719).sum := by decide
  have hdescent : baseEnd_478719 < baseStart_478719 := by decide
  rcases family_descends (prefixWord ++ tailWord_478719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478753 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 6]
def baseStart_478753 : Nat := 118140960795 + 478753 * 2 ^ 59
def prefixEnd_478753 : Nat := 4983230072969 + 3 ^ 40 * 478753 * 2
def baseEnd_478753 : Nat := 27314489309118956709529

theorem tailTrace_478753 : CollatzResearch.WordTrace tailWord_478753 prefixEnd_478753 27314489309118956709529 := by
  unfold tailWord_478753
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461556434567120347904913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11641037623044746898603275 17461556434567120347904913)
  ·
    refine ⟨13096167325925340260928685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461556434567120347904913 13096167325925340260928685)
    ·
      refine ⟨4911062747222002597848257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13096167325925340260928685 4911062747222002597848257)
      ·
        refine ⟨3683297060416501948386193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911062747222002597848257 3683297060416501948386193)
        ·
          refine ⟨2762472795312376461289645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683297060416501948386193 2762472795312376461289645)
          ·
            refine ⟨1035927298242141172983617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2762472795312376461289645 1035927298242141172983617)
            ·
              refine ⟨776945473681605879737713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035927298242141172983617 776945473681605879737713)
              ·
                refine ⟨582709105261204409803285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776945473681605879737713 582709105261204409803285)
                ·
                  refine ⟨27314489309118956709529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 582709105261204409803285 27314489309118956709529)
                  ·
                    rfl

theorem cell23_478753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_478753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478753 prefixEnd_478753 := by exact prefixLift 478753
  have htrace : WordTrace (prefixWord ++ tailWord_478753) baseStart_478753 baseEnd_478753 := by
    simpa [prefixWord, tailWord_478753, baseEnd_478753] using wordTrace_append hprefix tailTrace_478753
  have hstable : (prefixWord ++ tailWord_478753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478753).length < 2 ^ (prefixWord ++ tailWord_478753).sum := by decide
  have hdescent : baseEnd_478753 < baseStart_478753 := by decide
  rcases family_descends (prefixWord ++ tailWord_478753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478816 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_478816 : Nat := 118140960795 + 478816 * 2 ^ 59
def prefixEnd_478816 : Nat := 4983230072969 + 3 ^ 40 * 478816 * 2
def baseEnd_478816 : Nat := 245862753063303863897971

theorem tailTrace_478816 : CollatzResearch.WordTrace tailWord_478816 prefixEnd_478816 245862753063303863897971 := by
  unfold tailWord_478816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731927116669441053724151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11642569488892588071632201 8731927116669441053724151)
  ·
    refine ⟨13097890675004161580586227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731927116669441053724151 13097890675004161580586227)
    ·
      refine ⟨19646836012506242370879341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097890675004161580586227 19646836012506242370879341)
      ·
        refine ⟨7367563504689840889079753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19646836012506242370879341 7367563504689840889079753)
        ·
          refine ⟨5525672628517380666809815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7367563504689840889079753 5525672628517380666809815)
          ·
            refine ⟨8288508942776071000214723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525672628517380666809815 8288508942776071000214723)
            ·
              refine ⟨12432763414164106500322085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8288508942776071000214723 12432763414164106500322085)
              ·
                refine ⟨2331143140155769968810391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12432763414164106500322085 2331143140155769968810391)
                ·
                  refine ⟨3496714710233654953215587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331143140155769968810391 3496714710233654953215587)
                  ·
                    refine ⟨5245072065350482429823381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3496714710233654953215587 5245072065350482429823381)
                    ·
                      refine ⟨245862753063303863897971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5245072065350482429823381 245862753063303863897971)
                      ·
                        rfl

theorem cell23_478816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_478816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478816 prefixEnd_478816 := by exact prefixLift 478816
  have htrace : WordTrace (prefixWord ++ tailWord_478816) baseStart_478816 baseEnd_478816 := by
    simpa [prefixWord, tailWord_478816, baseEnd_478816] using wordTrace_append hprefix tailTrace_478816
  have hstable : (prefixWord ++ tailWord_478816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478816).length < 2 ^ (prefixWord ++ tailWord_478816).sum := by decide
  have hdescent : baseEnd_478816 < baseStart_478816 := by decide
  rcases family_descends (prefixWord ++ tailWord_478816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478823 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_478823 : Nat := 118140960795 + 478823 * 2 ^ 59
def prefixEnd_478823 : Nat := 4983230072969 + 3 ^ 40 * 478823 * 2
def baseEnd_478823 : Nat := 245866347427885336510439

theorem tailTrace_478823 : CollatzResearch.WordTrace tailWord_478823 prefixEnd_478823 245866347427885336510439 := by
  unfold tailWord_478823
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464109544313522302953123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11642739696209014868635415 17464109544313522302953123)
  ·
    refine ⟨26196164316470283454429685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17464109544313522302953123 26196164316470283454429685)
    ·
      refine ⟨2455890404669089073852783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26196164316470283454429685 2455890404669089073852783)
      ·
        refine ⟨3683835607003633610779175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455890404669089073852783 3683835607003633610779175)
        ·
          refine ⟨5525753410505450416168763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683835607003633610779175 5525753410505450416168763)
          ·
            refine ⟨8288630115758175624253145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525753410505450416168763 8288630115758175624253145)
            ·
              refine ⟨6216472586818631718189859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288630115758175624253145 6216472586818631718189859)
              ·
                refine ⟨9324708880227947577284789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216472586818631718189859 9324708880227947577284789)
                ·
                  refine ⟨874191457521370085370449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9324708880227947577284789 874191457521370085370449)
                  ·
                    refine ⟨655643593141027564027837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874191457521370085370449 655643593141027564027837)
                    ·
                      refine ⟨245866347427885336510439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655643593141027564027837 245866347427885336510439)
                      ·
                        rfl

theorem cell23_478823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_478823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478823 prefixEnd_478823 := by exact prefixLift 478823
  have htrace : WordTrace (prefixWord ++ tailWord_478823) baseStart_478823 baseEnd_478823 := by
    simpa [prefixWord, tailWord_478823, baseEnd_478823] using wordTrace_append hprefix tailTrace_478823
  have hstable : (prefixWord ++ tailWord_478823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478823).length < 2 ^ (prefixWord ++ tailWord_478823).sum := by decide
  have hdescent : baseEnd_478823 < baseStart_478823 := by decide
  rcases family_descends (prefixWord ++ tailWord_478823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478837 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_478837 : Nat := 118140960795 + 478837 * 2 ^ 59
def prefixEnd_478837 : Nat := 4983230072969 + 3 ^ 40 * 478837 * 2
def baseEnd_478837 : Nat := 245873536157048281735375

theorem tailTrace_478837 : CollatzResearch.WordTrace tailWord_478837 prefixEnd_478837 245873536157048281735375 := by
  unfold tailWord_478837
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464620166262802693962765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11643080110841868462641843 17464620166262802693962765)
  ·
    refine ⟨6549232562348551010236037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17464620166262802693962765 6549232562348551010236037)
    ·
      refine ⟨1227981105440353314419257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6549232562348551010236037 1227981105440353314419257)
      ·
        refine ⟨920985829080264985814443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227981105440353314419257 920985829080264985814443)
        ·
          refine ⟨1381478743620397478721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920985829080264985814443 1381478743620397478721665)
          ·
            refine ⟨1036109057715298109041249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381478743620397478721665 1036109057715298109041249)
            ·
              refine ⟨777081793286473581780937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036109057715298109041249 777081793286473581780937)
              ·
                refine ⟨582811344964855186335703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777081793286473581780937 582811344964855186335703)
                ·
                  refine ⟨874217017447282779503555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582811344964855186335703 874217017447282779503555)
                  ·
                    refine ⟨1311325526170924169255333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 874217017447282779503555 1311325526170924169255333)
                    ·
                      refine ⟨245873536157048281735375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1311325526170924169255333 245873536157048281735375)
                      ·
                        rfl

theorem cell23_478837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_478837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478837 prefixEnd_478837 := by exact prefixLift 478837
  have htrace : WordTrace (prefixWord ++ tailWord_478837) baseStart_478837 baseEnd_478837 := by
    simpa [prefixWord, tailWord_478837, baseEnd_478837] using wordTrace_append hprefix tailTrace_478837
  have hstable : (prefixWord ++ tailWord_478837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478837).length < 2 ^ (prefixWord ++ tailWord_478837).sum := by decide
  have hdescent : baseEnd_478837 < baseStart_478837 := by decide
  rcases family_descends (prefixWord ++ tailWord_478837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478853 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_478853 : Nat := 118140960795 + 478853 * 2 ^ 59
def prefixEnd_478853 : Nat := 4983230072969 + 3 ^ 40 * 478853 * 2
def baseEnd_478853 : Nat := 245881751847520219135301

theorem tailTrace_478853 : CollatzResearch.WordTrace tailWord_478853 prefixEnd_478853 245881751847520219135301 := by
  unfold tailWord_478853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465203734204837426545213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11643469156136558284363475 17465203734204837426545213)
  ·
    refine ⟨6549451400326814034954455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17465203734204837426545213 6549451400326814034954455)
    ·
      refine ⟨9824177100490221052431683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6549451400326814034954455 9824177100490221052431683)
      ·
        refine ⟨14736265650735331578647525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9824177100490221052431683 14736265650735331578647525)
        ·
          refine ⟨2763049809512874670996411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14736265650735331578647525 2763049809512874670996411)
          ·
            refine ⟨4144574714269312006494617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763049809512874670996411 4144574714269312006494617)
            ·
              refine ⟨3108431035701984004870963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4144574714269312006494617 3108431035701984004870963)
              ·
                refine ⟨4662646553552976007306445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108431035701984004870963 4662646553552976007306445)
                ·
                  refine ⟨1748492457582366002739917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4662646553552976007306445 1748492457582366002739917)
                  ·
                    refine ⟨655684671593387251027469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748492457582366002739917 655684671593387251027469)
                    ·
                      refine ⟨245881751847520219135301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655684671593387251027469 245881751847520219135301)
                      ·
                        rfl

theorem cell23_478853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_478853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478853 prefixEnd_478853 := by exact prefixLift 478853
  have htrace : WordTrace (prefixWord ++ tailWord_478853) baseStart_478853 baseEnd_478853 := by
    simpa [prefixWord, tailWord_478853, baseEnd_478853] using wordTrace_append hprefix tailTrace_478853
  have hstable : (prefixWord ++ tailWord_478853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478853).length < 2 ^ (prefixWord ++ tailWord_478853).sum := by decide
  have hdescent : baseEnd_478853 < baseStart_478853 := by decide
  rcases family_descends (prefixWord ++ tailWord_478853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478871 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_478871 : Nat := 118140960795 + 478871 * 2 ^ 59
def prefixEnd_478871 : Nat := 4983230072969 + 3 ^ 40 * 478871 * 2
def baseEnd_478871 : Nat := 245890994499301148710219

theorem tailTrace_478871 : CollatzResearch.WordTrace tailWord_478871 prefixEnd_478871 245890994499301148710219 := by
  unfold tailWord_478871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465860248139626500700467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11643906832093084333800311 17465860248139626500700467)
  ·
    refine ⟨26198790372209439751050701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17465860248139626500700467 26198790372209439751050701)
    ·
      refine ⟨9824546389578539906644013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26198790372209439751050701 9824546389578539906644013)
      ·
        refine ⟨3684204896091952464991505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9824546389578539906644013 3684204896091952464991505)
        ·
          refine ⟨2763153672068964348743629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3684204896091952464991505 2763153672068964348743629)
          ·
            refine ⟨1036182627025861630778861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2763153672068964348743629 1036182627025861630778861)
            ·
              refine ⟨388568485134698111542073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1036182627025861630778861 388568485134698111542073)
              ·
                refine ⟨291426363851023583656555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388568485134698111542073 291426363851023583656555)
                ·
                  refine ⟨437139545776535375484833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291426363851023583656555 437139545776535375484833)
                  ·
                    refine ⟨327854659332401531613625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437139545776535375484833 327854659332401531613625)
                    ·
                      refine ⟨245890994499301148710219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 327854659332401531613625 245890994499301148710219)
                      ·
                        rfl

theorem cell23_478871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_478871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478871 prefixEnd_478871 := by exact prefixLift 478871
  have htrace : WordTrace (prefixWord ++ tailWord_478871) baseStart_478871 baseEnd_478871 := by
    simpa [prefixWord, tailWord_478871, baseEnd_478871] using wordTrace_append hprefix tailTrace_478871
  have hstable : (prefixWord ++ tailWord_478871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478871).length < 2 ^ (prefixWord ++ tailWord_478871).sum := by decide
  have hdescent : baseEnd_478871 < baseStart_478871 := by decide
  rcases family_descends (prefixWord ++ tailWord_478871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478888 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_478888 : Nat := 118140960795 + 478888 * 2 ^ 59
def prefixEnd_478888 : Nat := 4983230072969 + 3 ^ 40 * 478888 * 2
def baseEnd_478888 : Nat := 245899723670427582197641

theorem tailTrace_478888 : CollatzResearch.WordTrace tailWord_478888 prefixEnd_478888 245899723670427582197641 := by
  unfold tailWord_478888
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733240144539019202034659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11644320192718692269379545 8733240144539019202034659)
  ·
    refine ⟨13099860216808528803051989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8733240144539019202034659 13099860216808528803051989)
    ·
      refine ⟨307027973831449893821531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13099860216808528803051989 307027973831449893821531)
      ·
        refine ⟨460541960747174840732297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307027973831449893821531 460541960747174840732297)
        ·
          refine ⟨345406470560381130549223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460541960747174840732297 345406470560381130549223)
          ·
            refine ⟨518109705840571695823835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345406470560381130549223 518109705840571695823835)
            ·
              refine ⟨777164558760857543735753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518109705840571695823835 777164558760857543735753)
              ·
                refine ⟨582873419070643157801815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777164558760857543735753 582873419070643157801815)
                ·
                  refine ⟨874310128605964736702723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582873419070643157801815 874310128605964736702723)
                  ·
                    refine ⟨1311465192908947105054085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 874310128605964736702723 1311465192908947105054085)
                    ·
                      refine ⟨245899723670427582197641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1311465192908947105054085 245899723670427582197641)
                      ·
                        rfl

theorem cell23_478888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_478888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478888 prefixEnd_478888 := by exact prefixLift 478888
  have htrace : WordTrace (prefixWord ++ tailWord_478888) baseStart_478888 baseEnd_478888 := by
    simpa [prefixWord, tailWord_478888, baseEnd_478888] using wordTrace_append hprefix tailTrace_478888
  have hstable : (prefixWord ++ tailWord_478888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478888).length < 2 ^ (prefixWord ++ tailWord_478888).sum := by decide
  have hdescent : baseEnd_478888 < baseStart_478888 := by decide
  rcases family_descends (prefixWord ++ tailWord_478888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478930 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_478930 : Nat := 118140960795 + 478930 * 2 ^ 59
def prefixEnd_478930 : Nat := 4983230072969 + 3 ^ 40 * 478930 * 2
def baseEnd_478930 : Nat := 245921289857916417872447

theorem tailTrace_478930 : CollatzResearch.WordTrace tailWord_478930 prefixEnd_478930 245921289857916417872447 := by
  unfold tailWord_478930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367003038731469894274561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11645341436617253051398829 4367003038731469894274561)
  ·
    refine ⟨3275252279048602420705921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4367003038731469894274561 3275252279048602420705921)
    ·
      refine ⟨2456439209286451815529441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275252279048602420705921 2456439209286451815529441)
      ·
        refine ⟨1842329406964838861647081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2456439209286451815529441 1842329406964838861647081)
        ·
          refine ⟨1381747055223629146235311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842329406964838861647081 1381747055223629146235311)
          ·
            refine ⟨2072620582835443719352967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381747055223629146235311 2072620582835443719352967)
            ·
              refine ⟨3108930874253165579029451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072620582835443719352967 3108930874253165579029451)
              ·
                refine ⟨4663396311379748368544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108930874253165579029451 4663396311379748368544177)
                ·
                  refine ⟨3497547233534811276408133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663396311379748368544177 3497547233534811276408133)
                  ·
                    refine ⟨655790106287777114326525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3497547233534811276408133 655790106287777114326525)
                    ·
                      refine ⟨245921289857916417872447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655790106287777114326525 245921289857916417872447)
                      ·
                        rfl

theorem cell23_478930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_478930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478930 prefixEnd_478930 := by exact prefixLift 478930
  have htrace : WordTrace (prefixWord ++ tailWord_478930) baseStart_478930 baseEnd_478930 := by
    simpa [prefixWord, tailWord_478930, baseEnd_478930] using wordTrace_append hprefix tailTrace_478930
  have hstable : (prefixWord ++ tailWord_478930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478930).length < 2 ^ (prefixWord ++ tailWord_478930).sum := by decide
  have hdescent : baseEnd_478930 < baseStart_478930 := by decide
  rcases family_descends (prefixWord ++ tailWord_478930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_478973 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_478973 : Nat := 118140960795 + 478973 * 2 ^ 59
def prefixEnd_478973 : Nat := 4983230072969 + 3 ^ 40 * 478973 * 2
def baseEnd_478973 : Nat := 245943369526059749634749

theorem tailTrace_478973 : CollatzResearch.WordTrace tailWord_478973 prefixEnd_478973 245943369526059749634749 := by
  unfold tailWord_478973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17469580493770097920913573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11646386995846731947275715 17469580493770097920913573)
  ·
    refine ⟨3275546342581893360171295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17469580493770097920913573 3275546342581893360171295)
    ·
      refine ⟨4913319513872840040256943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275546342581893360171295 4913319513872840040256943)
      ·
        refine ⟨7369979270809260060385415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913319513872840040256943 7369979270809260060385415)
        ·
          refine ⟨11054968906213890090578123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369979270809260060385415 11054968906213890090578123)
          ·
            refine ⟨16582453359320835135867185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054968906213890090578123 16582453359320835135867185)
            ·
              refine ⟨12436840019490626351900389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16582453359320835135867185 12436840019490626351900389)
              ·
                refine ⟨2331907503654492440981323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12436840019490626351900389 2331907503654492440981323)
                ·
                  refine ⟨3497861255481738661471985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331907503654492440981323 3497861255481738661471985)
                  ·
                    refine ⟨2623395941611303996103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3497861255481738661471985 2623395941611303996103989)
                    ·
                      refine ⟨245943369526059749634749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2623395941611303996103989 245943369526059749634749)
                      ·
                        rfl

theorem cell23_478973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_478973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_478973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_478973 prefixEnd_478973 := by exact prefixLift 478973
  have htrace : WordTrace (prefixWord ++ tailWord_478973) baseStart_478973 baseEnd_478973 := by
    simpa [prefixWord, tailWord_478973, baseEnd_478973] using wordTrace_append hprefix tailTrace_478973
  have hstable : (prefixWord ++ tailWord_478973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_478973).length < 2 ^ (prefixWord ++ tailWord_478973).sum := by decide
  have hdescent : baseEnd_478973 < baseStart_478973 := by decide
  rcases family_descends (prefixWord ++ tailWord_478973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479020 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_479020 : Nat := 118140960795 + 479020 * 2 ^ 59
def prefixEnd_479020 : Nat := 4983230072969 + 3 ^ 40 * 479020 * 2
def baseEnd_479020 : Nat := 245967503116821065747033

theorem tailTrace_479020 : CollatzResearch.WordTrace tailWord_479020 prefixEnd_479020 245967503116821065747033 := by
  unfold tailWord_479020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735647362299912473937257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11647529816399883298583009 8735647362299912473937257)
  ·
    refine ⟨6551735521724934355452943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8735647362299912473937257 6551735521724934355452943)
    ·
      refine ⟨9827603282587401533179415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551735521724934355452943 9827603282587401533179415)
      ·
        refine ⟨14741404923881102299769123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827603282587401533179415 14741404923881102299769123)
        ·
          refine ⟨22112107385821653449653685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741404923881102299769123 22112107385821653449653685)
          ·
            refine ⟨2073010067420780010905033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22112107385821653449653685 2073010067420780010905033)
            ·
              refine ⟨1554757550565585008178775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073010067420780010905033 1554757550565585008178775)
              ·
                refine ⟨2332136325848377512268163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554757550565585008178775 2332136325848377512268163)
                ·
                  refine ⟨3498204488772566268402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332136325848377512268163 3498204488772566268402245)
                  ·
                    refine ⟨655913341644856175325421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498204488772566268402245 655913341644856175325421)
                    ·
                      refine ⟨245967503116821065747033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655913341644856175325421 245967503116821065747033)
                      ·
                        rfl

theorem cell23_479020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_479020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479020 prefixEnd_479020 := by exact prefixLift 479020
  have htrace : WordTrace (prefixWord ++ tailWord_479020) baseStart_479020 baseEnd_479020 := by
    simpa [prefixWord, tailWord_479020, baseEnd_479020] using wordTrace_append hprefix tailTrace_479020
  have hstable : (prefixWord ++ tailWord_479020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479020).length < 2 ^ (prefixWord ++ tailWord_479020).sum := by decide
  have hdescent : baseEnd_479020 < baseStart_479020 := by decide
  rcases family_descends (prefixWord ++ tailWord_479020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479037 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_479037 : Nat := 118140960795 + 479037 * 2 ^ 59
def prefixEnd_479037 : Nat := 4983230072969 + 3 ^ 40 * 479037 * 2
def baseEnd_479037 : Nat := 245976232287947499234455

theorem tailTrace_479037 : CollatzResearch.WordTrace tailWord_479037 prefixEnd_479037 245976232287947499234455 := by
  unfold tailWord_479037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17471914765538236851243365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11647943177025491234162243 17471914765538236851243365)
  ·
    refine ⟨3275984018538419409608131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17471914765538236851243365 3275984018538419409608131)
    ·
      refine ⟨4913976027807629114412197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275984018538419409608131 4913976027807629114412197)
      ·
        refine ⟨921370505213930458952287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4913976027807629114412197 921370505213930458952287)
        ·
          refine ⟨1382055757820895688428431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921370505213930458952287 1382055757820895688428431)
          ·
            refine ⟨2073083636731343532642647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382055757820895688428431 2073083636731343532642647)
            ·
              refine ⟨3109625455097015298963971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073083636731343532642647 3109625455097015298963971)
              ·
                refine ⟨4664438182645522948445957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109625455097015298963971 4664438182645522948445957)
                ·
                  refine ⟨874582159246035552833617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4664438182645522948445957 874582159246035552833617)
                  ·
                    refine ⟨655936619434526664625213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874582159246035552833617 655936619434526664625213)
                    ·
                      refine ⟨245976232287947499234455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 655936619434526664625213 245976232287947499234455)
                      ·
                        rfl

theorem cell23_479037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_479037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479037 prefixEnd_479037 := by exact prefixLift 479037
  have htrace : WordTrace (prefixWord ++ tailWord_479037) baseStart_479037 baseEnd_479037 := by
    simpa [prefixWord, tailWord_479037, baseEnd_479037] using wordTrace_append hprefix tailTrace_479037
  have hstable : (prefixWord ++ tailWord_479037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479037).length < 2 ^ (prefixWord ++ tailWord_479037).sum := by decide
  have hdescent : baseEnd_479037 < baseStart_479037 := by decide
  rcases family_descends (prefixWord ++ tailWord_479037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479057 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 6]
def baseStart_479057 : Nat := 118140960795 + 479057 * 2 ^ 59
def prefixEnd_479057 : Nat := 4983230072969 + 3 ^ 40 * 479057 * 2
def baseEnd_479057 : Nat := 27331833544559713442707

theorem tailTrace_479057 : CollatzResearch.WordTrace tailWord_479057 prefixEnd_479057 27331833544559713442707 := by
  unfold tailWord_479057
  simp only [CollatzResearch.WordTrace]
  refine ⟨17472644225465780266971425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11648429483643853511314283 17472644225465780266971425)
  ·
    refine ⟨13104483169099335200228569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17472644225465780266971425 13104483169099335200228569)
    ·
      refine ⟨9828362376824501400171427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13104483169099335200228569 9828362376824501400171427)
      ·
        refine ⟨14742543565236752100257141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828362376824501400171427 14742543565236752100257141)
        ·
          refine ⟨1382113459240945509399107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14742543565236752100257141 1382113459240945509399107)
          ·
            refine ⟨2073170188861418264098661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382113459240945509399107 2073170188861418264098661)
            ·
              refine ⟨388719410411515924518499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2073170188861418264098661 388719410411515924518499)
              ·
                refine ⟨583079115617273886777749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388719410411515924518499 583079115617273886777749)
                ·
                  refine ⟨27331833544559713442707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 583079115617273886777749 27331833544559713442707)
                  ·
                    rfl

theorem cell23_479057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_479057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479057 prefixEnd_479057 := by exact prefixLift 479057
  have htrace : WordTrace (prefixWord ++ tailWord_479057) baseStart_479057 baseEnd_479057 := by
    simpa [prefixWord, tailWord_479057, baseEnd_479057] using wordTrace_append hprefix tailTrace_479057
  have hstable : (prefixWord ++ tailWord_479057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479057).length < 2 ^ (prefixWord ++ tailWord_479057).sum := by decide
  have hdescent : baseEnd_479057 < baseStart_479057 := by decide
  rcases family_descends (prefixWord ++ tailWord_479057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479120 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_479120 : Nat := 118140960795 + 479120 * 2 ^ 59
def prefixEnd_479120 : Nat := 4983230072969 + 3 ^ 40 * 479120 * 2
def baseEnd_479120 : Nat := 246018851182270674496573

theorem tailTrace_479120 : CollatzResearch.WordTrace tailWord_479120 prefixEnd_479120 246018851182270674496573 := by
  unfold tailWord_479120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8737471012118771013257407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11649961349491694684343209 8737471012118771013257407)
  ·
    refine ⟨13106206518178156519886111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8737471012118771013257407 13106206518178156519886111)
    ·
      refine ⟨19659309777267234779829167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13106206518178156519886111 19659309777267234779829167)
      ·
        refine ⟨29488964665900852169743751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19659309777267234779829167 29488964665900852169743751)
        ·
          refine ⟨44233446998851278254615627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29488964665900852169743751 44233446998851278254615627)
          ·
            refine ⟨66350170498276917381923441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44233446998851278254615627 66350170498276917381923441)
            ·
              refine ⟨49762627873707688036442581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66350170498276917381923441 49762627873707688036442581)
              ·
                refine ⟨1166311590790023938354123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49762627873707688036442581 1166311590790023938354123)
                ·
                  refine ⟨1749467386185035907531185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166311590790023938354123 1749467386185035907531185)
                  ·
                    refine ⟨1312100539638776930648389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1749467386185035907531185 1312100539638776930648389)
                    ·
                      refine ⟨246018851182270674496573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1312100539638776930648389 246018851182270674496573)
                      ·
                        rfl

theorem cell23_479120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_479120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479120 prefixEnd_479120 := by exact prefixLift 479120
  have htrace : WordTrace (prefixWord ++ tailWord_479120) baseStart_479120 baseEnd_479120 := by
    simpa [prefixWord, tailWord_479120, baseEnd_479120] using wordTrace_append hprefix tailTrace_479120
  have hstable : (prefixWord ++ tailWord_479120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479120).length < 2 ^ (prefixWord ++ tailWord_479120).sum := by decide
  have hdescent : baseEnd_479120 < baseStart_479120 := by decide
  rcases family_descends (prefixWord ++ tailWord_479120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479127 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_479127 : Nat := 118140960795 + 479127 * 2 ^ 59
def prefixEnd_479127 : Nat := 4983230072969 + 3 ^ 40 * 479127 * 2
def baseEnd_479127 : Nat := 246022445546852147109041

theorem tailTrace_479127 : CollatzResearch.WordTrace tailWord_479127 prefixEnd_479127 246022445546852147109041 := by
  unfold tailWord_479127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17475197335212182222019635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11650131556808121481346423 17475197335212182222019635)
  ·
    refine ⟨26212796002818273333029453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17475197335212182222019635 26212796002818273333029453)
    ·
      refine ⟨9829798501056852499886045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26212796002818273333029453 9829798501056852499886045)
      ·
        refine ⟨3686174437896319687457267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9829798501056852499886045 3686174437896319687457267)
        ·
          refine ⟨5529261656844479531185901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686174437896319687457267 5529261656844479531185901)
          ·
            refine ⟨2073473121316679824194713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5529261656844479531185901 2073473121316679824194713)
            ·
              refine ⟨1555104840987509868146035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073473121316679824194713 1555104840987509868146035)
              ·
                refine ⟨2332657261481264802219053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555104840987509868146035 2332657261481264802219053)
                ·
                  refine ⟨874746473055474300832145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2332657261481264802219053 874746473055474300832145)
                  ·
                    refine ⟨656059854791605725624109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874746473055474300832145 656059854791605725624109)
                    ·
                      refine ⟨246022445546852147109041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 656059854791605725624109 246022445546852147109041)
                      ·
                        rfl

theorem cell23_479127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_479127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479127 prefixEnd_479127 := by exact prefixLift 479127
  have htrace : WordTrace (prefixWord ++ tailWord_479127) baseStart_479127 baseEnd_479127 := by
    simpa [prefixWord, tailWord_479127, baseEnd_479127] using wordTrace_append hprefix tailTrace_479127
  have hstable : (prefixWord ++ tailWord_479127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479127).length < 2 ^ (prefixWord ++ tailWord_479127).sum := by decide
  have hdescent : baseEnd_479127 < baseStart_479127 := by decide
  rcases family_descends (prefixWord ++ tailWord_479127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479128 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_479128 : Nat := 118140960795 + 479128 * 2 ^ 59
def prefixEnd_479128 : Nat := 4983230072969 + 3 ^ 40 * 479128 * 2
def baseEnd_479128 : Nat := 246022959027506643196537

theorem tailTrace_479128 : CollatzResearch.WordTrace tailWord_479128 prefixEnd_479128 246022959027506643196537 := by
  unfold tailWord_479128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8737616904104279696403019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11650155872139039595204025 8737616904104279696403019)
  ·
    refine ⟨13106425356156419544604529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8737616904104279696403019 13106425356156419544604529)
    ·
      refine ⟨9829819017117314658453397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13106425356156419544604529 9829819017117314658453397)
      ·
        refine ⟨460772766427374124615003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9829819017117314658453397 460772766427374124615003)
        ·
          refine ⟨691159149641061186922505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460772766427374124615003 691159149641061186922505)
          ·
            refine ⟨518369362230795890191879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691159149641061186922505 518369362230795890191879)
            ·
              refine ⟨777554043346193835287819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518369362230795890191879 777554043346193835287819)
              ·
                refine ⟨1166331065019290752931729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777554043346193835287819 1166331065019290752931729)
                ·
                  refine ⟨874748298764468064698797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166331065019290752931729 874748298764468064698797)
                  ·
                    refine ⟨328030612036675524262049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874748298764468064698797 328030612036675524262049)
                    ·
                      refine ⟨246022959027506643196537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328030612036675524262049 246022959027506643196537)
                      ·
                        rfl

theorem cell23_479128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_479128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479128 prefixEnd_479128 := by exact prefixLift 479128
  have htrace : WordTrace (prefixWord ++ tailWord_479128) baseStart_479128 baseEnd_479128 := by
    simpa [prefixWord, tailWord_479128, baseEnd_479128] using wordTrace_append hprefix tailTrace_479128
  have hstable : (prefixWord ++ tailWord_479128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479128).length < 2 ^ (prefixWord ++ tailWord_479128).sum := by decide
  have hdescent : baseEnd_479128 < baseStart_479128 := by decide
  rcases family_descends (prefixWord ++ tailWord_479128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479138 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_479138 : Nat := 118140960795 + 479138 * 2 ^ 59
def prefixEnd_479138 : Nat := 4983230072969 + 3 ^ 40 * 479138 * 2
def baseEnd_479138 : Nat := 82009364611350534690497

theorem tailTrace_479138 : CollatzResearch.WordTrace tailWord_479138 prefixEnd_479138 82009364611350534690497 := by
  unfold tailWord_479138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368899634543082775167517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11650399025448220733780045 4368899634543082775167517)
  ·
    refine ⟨1638337362953656040687819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4368899634543082775167517 1638337362953656040687819)
    ·
      refine ⟨2457506044430484061031729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638337362953656040687819 2457506044430484061031729)
      ·
        refine ⟨1843129533322863045773797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2457506044430484061031729 1843129533322863045773797)
        ·
          refine ⟨345586787498036821082587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1843129533322863045773797 345586787498036821082587)
          ·
            refine ⟨518380181247055231623881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345586787498036821082587 518380181247055231623881)
            ·
              refine ⟨388785135935291423717911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518380181247055231623881 388785135935291423717911)
              ·
                refine ⟨583177703902937135576867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388785135935291423717911 583177703902937135576867)
                ·
                  refine ⟨874766555854405703365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583177703902937135576867 874766555854405703365301)
                  ·
                    refine ⟨82009364611350534690497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 874766555854405703365301 82009364611350534690497)
                    ·
                      rfl

theorem cell23_479138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_479138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479138 prefixEnd_479138 := by exact prefixLift 479138
  have htrace : WordTrace (prefixWord ++ tailWord_479138) baseStart_479138 baseEnd_479138 := by
    simpa [prefixWord, tailWord_479138, baseEnd_479138] using wordTrace_append hprefix tailTrace_479138
  have hstable : (prefixWord ++ tailWord_479138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479138).length < 2 ^ (prefixWord ++ tailWord_479138).sum := by decide
  have hdescent : baseEnd_479138 < baseStart_479138 := by decide
  rcases family_descends (prefixWord ++ tailWord_479138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479184 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2]
def baseStart_479184 : Nat := 118140960795 + 479184 * 2 ^ 59
def prefixEnd_479184 : Nat := 4983230072969 + 3 ^ 40 * 479184 * 2
def baseEnd_479184 : Nat := 246051713944158424096279

theorem tailTrace_479184 : CollatzResearch.WordTrace tailWord_479184 prefixEnd_479184 246051713944158424096279 := by
  unfold tailWord_479184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738638148002840478422303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11651517530670453971229737 8738638148002840478422303)
  ·
    refine ⟨13107957222004260717633455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8738638148002840478422303 13107957222004260717633455)
    ·
      refine ⟨19661935833006391076450183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107957222004260717633455 19661935833006391076450183)
      ·
        refine ⟨29492903749509586614675275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19661935833006391076450183 29492903749509586614675275)
        ·
          refine ⟨44239355624264379922012913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29492903749509586614675275 44239355624264379922012913)
          ·
            refine ⟨33179516718198284941509685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44239355624264379922012913 33179516718198284941509685)
            ·
              refine ⟨3110579692331089213266533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33179516718198284941509685 3110579692331089213266533)
              ·
                refine ⟨583233692312079227487475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3110579692331089213266533 583233692312079227487475)
                ·
                  refine ⟨874850538468118841231213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583233692312079227487475 874850538468118841231213)
                  ·
                    refine ⟨328068951925544565461705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874850538468118841231213 328068951925544565461705)
                    ·
                      refine ⟨246051713944158424096279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328068951925544565461705 246051713944158424096279)
                      ·
                        rfl

theorem cell23_479184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2].length) (baseStart_479184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479184 prefixEnd_479184 := by exact prefixLift 479184
  have htrace : WordTrace (prefixWord ++ tailWord_479184) baseStart_479184 baseEnd_479184 := by
    simpa [prefixWord, tailWord_479184, baseEnd_479184] using wordTrace_append hprefix tailTrace_479184
  have hstable : (prefixWord ++ tailWord_479184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479184).length < 2 ^ (prefixWord ++ tailWord_479184).sum := by decide
  have hdescent : baseEnd_479184 < baseStart_479184 := by decide
  rcases family_descends (prefixWord ++ tailWord_479184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479252 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_479252 : Nat := 118140960795 + 479252 * 2 ^ 59
def prefixEnd_479252 : Nat := 4983230072969 + 3 ^ 40 * 479252 * 2
def baseEnd_479252 : Nat := 246086630628664158045967

theorem tailTrace_479252 : CollatzResearch.WordTrace tailWord_479252 prefixEnd_479252 246086630628664158045967 := by
  unfold tailWord_479252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739878229879664285160005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11653170973172885713546673 8739878229879664285160005)
  ·
    refine ⟨1638727168102437053467501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8739878229879664285160005 1638727168102437053467501)
    ·
      refine ⟨614522688038413895050313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1638727168102437053467501 614522688038413895050313)
      ·
        refine ⟨460892016028810421287735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614522688038413895050313 460892016028810421287735)
        ·
          refine ⟨691338024043215631931603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460892016028810421287735 691338024043215631931603)
          ·
            refine ⟨1037007036064823447897405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691338024043215631931603 1037007036064823447897405)
            ·
              refine ⟨388877638524308792961527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037007036064823447897405 388877638524308792961527)
              ·
                refine ⟨583316457786463189442291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388877638524308792961527 583316457786463189442291)
                ·
                  refine ⟨874974686679694784163437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583316457786463189442291 874974686679694784163437)
                  ·
                    refine ⟨328115507504885544061289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874974686679694784163437 328115507504885544061289)
                    ·
                      refine ⟨246086630628664158045967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328115507504885544061289 246086630628664158045967)
                      ·
                        rfl

theorem cell23_479252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_479252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479252 prefixEnd_479252 := by exact prefixLift 479252
  have htrace : WordTrace (prefixWord ++ tailWord_479252) baseStart_479252 baseEnd_479252 := by
    simpa [prefixWord, tailWord_479252, baseEnd_479252] using wordTrace_append hprefix tailTrace_479252
  have hstable : (prefixWord ++ tailWord_479252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479252).length < 2 ^ (prefixWord ++ tailWord_479252).sum := by decide
  have hdescent : baseEnd_479252 < baseStart_479252 := by decide
  rcases family_descends (prefixWord ++ tailWord_479252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479267 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 2, 5]
def baseStart_479267 : Nat := 118140960795 + 479267 * 2 ^ 59
def prefixEnd_479267 : Nat := 4983230072969 + 3 ^ 40 * 479267 * 2
def baseEnd_479267 : Nat := 82031444279493866452799

theorem tailTrace_479267 : CollatzResearch.WordTrace tailWord_479267 prefixEnd_479267 82031444279493866452799 := by
  unfold tailWord_479267
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480303554704986132116055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11653535703136657421410703 17480303554704986132116055)
  ·
    refine ⟨26220455332057479198174083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480303554704986132116055 26220455332057479198174083)
    ·
      refine ⟨39330682998086218797261125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26220455332057479198174083 39330682998086218797261125)
      ·
        refine ⟨7374503062141166024486461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39330682998086218797261125 7374503062141166024486461)
        ·
          refine ⟨2765438648302937259182423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7374503062141166024486461 2765438648302937259182423)
          ·
            refine ⟨4148157972454405888773635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765438648302937259182423 4148157972454405888773635)
            ·
              refine ⟨6222236958681608833160453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148157972454405888773635 6222236958681608833160453)
              ·
                refine ⟨1166669429752801656217585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6222236958681608833160453 1166669429752801656217585)
                ·
                  refine ⟨875002072314601242163189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166669429752801656217585 875002072314601242163189)
                  ·
                    refine ⟨82031444279493866452799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875002072314601242163189 82031444279493866452799)
                    ·
                      rfl

theorem cell23_479267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 5].length) (baseStart_479267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479267 prefixEnd_479267 := by exact prefixLift 479267
  have htrace : WordTrace (prefixWord ++ tailWord_479267) baseStart_479267 baseEnd_479267 := by
    simpa [prefixWord, tailWord_479267, baseEnd_479267] using wordTrace_append hprefix tailTrace_479267
  have hstable : (prefixWord ++ tailWord_479267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479267).length < 2 ^ (prefixWord ++ tailWord_479267).sum := by decide
  have hdescent : baseEnd_479267 < baseStart_479267 := by decide
  rcases family_descends (prefixWord ++ tailWord_479267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479287 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_479287 : Nat := 118140960795 + 479287 * 2 ^ 59
def prefixEnd_479287 : Nat := 4983230072969 + 3 ^ 40 * 479287 * 2
def baseEnd_479287 : Nat := 246104602451571521108305

theorem tailTrace_479287 : CollatzResearch.WordTrace tailWord_479287 prefixEnd_479287 246104602451571521108305 := by
  unfold tailWord_479287
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481033014632529547844115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11654022009755019698562743 17481033014632529547844115)
  ·
    refine ⟨26221549521948794321766173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17481033014632529547844115 26221549521948794321766173)
    ·
      refine ⟨9833081070730797870662315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26221549521948794321766173 9833081070730797870662315)
      ·
        refine ⟨14749621606096196805993473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833081070730797870662315 14749621606096196805993473)
        ·
          refine ⟨11062216204572147604495105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14749621606096196805993473 11062216204572147604495105)
          ·
            refine ⟨8296662153429110703371329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11062216204572147604495105 8296662153429110703371329)
            ·
              refine ⟨6222496615071833027528497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296662153429110703371329 6222496615071833027528497)
              ·
                refine ⟨4666872461303874770646373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222496615071833027528497 4666872461303874770646373)
                ·
                  refine ⟨875038586494476519496195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4666872461303874770646373 875038586494476519496195)
                  ·
                    refine ⟨1312557879741714779244293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875038586494476519496195 1312557879741714779244293)
                    ·
                      refine ⟨246104602451571521108305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1312557879741714779244293 246104602451571521108305)
                      ·
                        rfl

theorem cell23_479287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_479287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479287 prefixEnd_479287 := by exact prefixLift 479287
  have htrace : WordTrace (prefixWord ++ tailWord_479287) baseStart_479287 baseEnd_479287 := by
    simpa [prefixWord, tailWord_479287, baseEnd_479287] using wordTrace_append hprefix tailTrace_479287
  have hstable : (prefixWord ++ tailWord_479287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479287).length < 2 ^ (prefixWord ++ tailWord_479287).sum := by decide
  have hdescent : baseEnd_479287 < baseStart_479287 := by decide
  rcases family_descends (prefixWord ++ tailWord_479287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479307 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3]
def baseStart_479307 : Nat := 118140960795 + 479307 * 2 ^ 59
def prefixEnd_479307 : Nat := 4983230072969 + 3 ^ 40 * 479307 * 2
def baseEnd_479307 : Nat := 246114872064661442858213

theorem tailTrace_479307 : CollatzResearch.WordTrace tailWord_479307 prefixEnd_479307 246114872064661442858213 := by
  unfold tailWord_479307
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481762474560072963572175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11654508316373381975714783 17481762474560072963572175)
  ·
    refine ⟨26222643711840109445358263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17481762474560072963572175 26222643711840109445358263)
    ·
      refine ⟨39333965567760164168037395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26222643711840109445358263 39333965567760164168037395)
      ·
        refine ⟨59000948351640246252056093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39333965567760164168037395 59000948351640246252056093)
        ·
          refine ⟨22125355631865092344521035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59000948351640246252056093 22125355631865092344521035)
          ·
            refine ⟨33188033447797638516781553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22125355631865092344521035 33188033447797638516781553)
            ·
              refine ⟨24891025085848228887586165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33188033447797638516781553 24891025085848228887586165)
              ·
                refine ⟨2333533601798271458211203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24891025085848228887586165 2333533601798271458211203)
                ·
                  refine ⟨3500300402697407187316805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333533601798271458211203 3500300402697407187316805)
                  ·
                    refine ⟨656306325505763847621901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3500300402697407187316805 656306325505763847621901)
                    ·
                      refine ⟨246114872064661442858213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 656306325505763847621901 246114872064661442858213)
                      ·
                        rfl

theorem cell23_479307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 3].length) (baseStart_479307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479307 prefixEnd_479307 := by exact prefixLift 479307
  have htrace : WordTrace (prefixWord ++ tailWord_479307) baseStart_479307 baseEnd_479307 := by
    simpa [prefixWord, tailWord_479307, baseEnd_479307] using wordTrace_append hprefix tailTrace_479307
  have hstable : (prefixWord ++ tailWord_479307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479307).length < 2 ^ (prefixWord ++ tailWord_479307).sum := by decide
  have hdescent : baseEnd_479307 < baseStart_479307 := by decide
  rcases family_descends (prefixWord ++ tailWord_479307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479317 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_479317 : Nat := 118140960795 + 479317 * 2 ^ 59
def prefixEnd_479317 : Nat := 4983230072969 + 3 ^ 40 * 479317 * 2
def baseEnd_479317 : Nat := 246120006871206403733167

theorem tailTrace_479317 : CollatzResearch.WordTrace tailWord_479317 prefixEnd_479317 246120006871206403733167 := by
  unfold tailWord_479317
  simp only [CollatzResearch.WordTrace]
  refine ⟨17482127204523844671436205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11654751469682563114290803 17482127204523844671436205)
  ·
    refine ⟨6555797701696441751788577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17482127204523844671436205 6555797701696441751788577)
    ·
      refine ⟨4916848276272331313841433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6555797701696441751788577 4916848276272331313841433)
      ·
        refine ⟨3687636207204248485381075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4916848276272331313841433 3687636207204248485381075)
        ·
          refine ⟨5531454310806372728071613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687636207204248485381075 5531454310806372728071613)
          ·
            refine ⟨2074295366552389773026855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5531454310806372728071613 2074295366552389773026855)
            ·
              refine ⟨3111443049828584659540283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074295366552389773026855 3111443049828584659540283)
              ·
                refine ⟨4667164574742876989310425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111443049828584659540283 4667164574742876989310425)
                ·
                  refine ⟨3500373431057157741982819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667164574742876989310425 3500373431057157741982819)
                  ·
                    refine ⟨5250560146585736612974229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500373431057157741982819 5250560146585736612974229)
                    ·
                      refine ⟨246120006871206403733167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5250560146585736612974229 246120006871206403733167)
                      ·
                        rfl

theorem cell23_479317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_479317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479317 prefixEnd_479317 := by exact prefixLift 479317
  have htrace : WordTrace (prefixWord ++ tailWord_479317) baseStart_479317 baseEnd_479317 := by
    simpa [prefixWord, tailWord_479317, baseEnd_479317] using wordTrace_append hprefix tailTrace_479317
  have hstable : (prefixWord ++ tailWord_479317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479317).length < 2 ^ (prefixWord ++ tailWord_479317).sum := by decide
  have hdescent : baseEnd_479317 < baseStart_479317 := by decide
  rcases family_descends (prefixWord ++ tailWord_479317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479327 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 6]
def baseStart_479327 : Nat := 118140960795 + 479327 * 2 ^ 59
def prefixEnd_479327 : Nat := 4983230072969 + 3 ^ 40 * 479327 * 2
def baseEnd_479327 : Nat := 27347237964194596067569

theorem tailTrace_479327 : CollatzResearch.WordTrace tailWord_479327 prefixEnd_479327 27347237964194596067569 := by
  unfold tailWord_479327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17482491934487616379300235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11654994622991744252866823 17482491934487616379300235)
  ·
    refine ⟨26223737901731424568950353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17482491934487616379300235 26223737901731424568950353)
    ·
      refine ⟨19667803426298568426712765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26223737901731424568950353 19667803426298568426712765)
      ·
        refine ⟨7375426284861963160017287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19667803426298568426712765 7375426284861963160017287)
        ·
          refine ⟨11063139427292944740025931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375426284861963160017287 11063139427292944740025931)
          ·
            refine ⟨16594709140939417110038897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063139427292944740025931 16594709140939417110038897)
            ·
              refine ⟨12446031855704562832529173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16594709140939417110038897 12446031855704562832529173)
              ·
                refine ⟨583407743236151382774805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12446031855704562832529173 583407743236151382774805)
                ·
                  refine ⟨27347237964194596067569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 583407743236151382774805 27347237964194596067569)
                  ·
                    rfl

theorem cell23_479327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 6].length) (baseStart_479327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479327 prefixEnd_479327 := by exact prefixLift 479327
  have htrace : WordTrace (prefixWord ++ tailWord_479327) baseStart_479327 baseEnd_479327 := by
    simpa [prefixWord, tailWord_479327, baseEnd_479327] using wordTrace_append hprefix tailTrace_479327
  have hstable : (prefixWord ++ tailWord_479327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479327).length < 2 ^ (prefixWord ++ tailWord_479327).sum := by decide
  have hdescent : baseEnd_479327 < baseStart_479327 := by decide
  rcases family_descends (prefixWord ++ tailWord_479327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479331 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 1, 4]
def baseStart_479331 : Nat := 118140960795 + 479331 * 2 ^ 59
def prefixEnd_479331 : Nat := 4983230072969 + 3 ^ 40 * 479331 * 2
def baseEnd_479331 : Nat := 82042398533456449652701

theorem tailTrace_479331 : CollatzResearch.WordTrace tailWord_479331 prefixEnd_479331 82042398533456449652701 := by
  unfold tailWord_479331
  simp only [CollatzResearch.WordTrace]
  refine ⟨17482637826473125062445847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11655091884315416708297231 17482637826473125062445847)
  ·
    refine ⟨26223956739709687593668771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17482637826473125062445847 26223956739709687593668771)
    ·
      refine ⟨39335935109564531390503157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26223956739709687593668771 39335935109564531390503157)
      ·
        refine ⟨3687743916521674817859671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39335935109564531390503157 3687743916521674817859671)
        ·
          refine ⟨5531615874782512226789507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687743916521674817859671 5531615874782512226789507)
          ·
            refine ⟨8297423812173768340184261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531615874782512226789507 8297423812173768340184261)
            ·
              refine ⟨1555766964782581563784549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8297423812173768340184261 1555766964782581563784549)
              ·
                refine ⟨291706305896734043209603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1555766964782581563784549 291706305896734043209603)
                ·
                  refine ⟨437559458845101064814405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291706305896734043209603 437559458845101064814405)
                  ·
                    refine ⟨82042398533456449652701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437559458845101064814405 82042398533456449652701)
                    ·
                      rfl

theorem cell23_479331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 4].length) (baseStart_479331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479331 prefixEnd_479331 := by exact prefixLift 479331
  have htrace : WordTrace (prefixWord ++ tailWord_479331) baseStart_479331 baseEnd_479331 := by
    simpa [prefixWord, tailWord_479331, baseEnd_479331] using wordTrace_append hprefix tailTrace_479331
  have hstable : (prefixWord ++ tailWord_479331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479331).length < 2 ^ (prefixWord ++ tailWord_479331).sum := by decide
  have hdescent : baseEnd_479331 < baseStart_479331 := by decide
  rcases family_descends (prefixWord ++ tailWord_479331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479381 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_479381 : Nat := 118140960795 + 479381 * 2 ^ 59
def prefixEnd_479381 : Nat := 4983230072969 + 3 ^ 40 * 479381 * 2
def baseEnd_479381 : Nat := 246152869633094153332873

theorem tailTrace_479381 : CollatzResearch.WordTrace tailWord_479381 prefixEnd_479381 246152869633094153332873 := by
  unfold tailWord_479381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484461476291983601765997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11656307650861322401177331 17484461476291983601765997)
  ·
    refine ⟨6556673053609493850662249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17484461476291983601765997 6556673053609493850662249)
    ·
      refine ⟨4917504790207120387996687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6556673053609493850662249 4917504790207120387996687)
      ·
        refine ⟨7376257185310680581995031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917504790207120387996687 7376257185310680581995031)
        ·
          refine ⟨11064385777966020872992547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376257185310680581995031 11064385777966020872992547)
          ·
            refine ⟨16596578666949031309488821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064385777966020872992547 16596578666949031309488821)
            ·
              refine ⟨1555929250026471685264577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16596578666949031309488821 1555929250026471685264577)
              ·
                refine ⟨1166946937519853763948433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555929250026471685264577 1166946937519853763948433)
                ·
                  refine ⟨875210203139890322961325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166946937519853763948433 875210203139890322961325)
                  ·
                    refine ⟨328203826177458871110497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875210203139890322961325 328203826177458871110497)
                    ·
                      refine ⟨246152869633094153332873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328203826177458871110497 246152869633094153332873)
                      ·
                        rfl

theorem cell23_479381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_479381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479381 prefixEnd_479381 := by exact prefixLift 479381
  have htrace : WordTrace (prefixWord ++ tailWord_479381) baseStart_479381 baseEnd_479381 := by
    simpa [prefixWord, tailWord_479381, baseEnd_479381] using wordTrace_append hprefix tailTrace_479381
  have hstable : (prefixWord ++ tailWord_479381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479381).length < 2 ^ (prefixWord ++ tailWord_479381).sum := by decide
  have hdescent : baseEnd_479381 < baseStart_479381 := by decide
  rcases family_descends (prefixWord ++ tailWord_479381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479411 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 5, 2, 2]
def baseStart_479411 : Nat := 118140960795 + 479411 * 2 ^ 59
def prefixEnd_479411 : Nat := 4983230072969 + 3 ^ 40 * 479411 * 2
def baseEnd_479411 : Nat := 246168274052729035957735

theorem tailTrace_479411 : CollatzResearch.WordTrace tailWord_479411 prefixEnd_479411 246168274052729035957735 := by
  unfold tailWord_479411
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485555666183298725358087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11657037110788865816905391 17485555666183298725358087)
  ·
    refine ⟨26228333499274948088037131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485555666183298725358087 26228333499274948088037131)
    ·
      refine ⟨39342500248912422132055697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26228333499274948088037131 39342500248912422132055697)
      ·
        refine ⟨29506875186684316599041773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39342500248912422132055697 29506875186684316599041773)
        ·
          refine ⟨11065078195006618724640665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29506875186684316599041773 11065078195006618724640665)
          ·
            refine ⟨8298808646254964043480499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065078195006618724640665 8298808646254964043480499)
            ·
              refine ⟨12448212969382446065220749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298808646254964043480499 12448212969382446065220749)
              ·
                refine ⟨4668079863518417274457781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12448212969382446065220749 4668079863518417274457781)
                ·
                  refine ⟨437632487204851619480417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4668079863518417274457781 437632487204851619480417)
                  ·
                    refine ⟨328224365403638714610313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437632487204851619480417 328224365403638714610313)
                    ·
                      refine ⟨246168274052729035957735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328224365403638714610313 246168274052729035957735)
                      ·
                        rfl

theorem cell23_479411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2, 2].length) (baseStart_479411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479411 prefixEnd_479411 := by exact prefixLift 479411
  have htrace : WordTrace (prefixWord ++ tailWord_479411) baseStart_479411 baseEnd_479411 := by
    simpa [prefixWord, tailWord_479411, baseEnd_479411] using wordTrace_append hprefix tailTrace_479411
  have hstable : (prefixWord ++ tailWord_479411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479411).length < 2 ^ (prefixWord ++ tailWord_479411).sum := by decide
  have hdescent : baseEnd_479411 < baseStart_479411 := by decide
  rcases family_descends (prefixWord ++ tailWord_479411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479417 : List Nat := [1, 2, 1, 4, 1, 2, 1, 11]
def baseStart_479417 : Nat := 118140960795 + 479417 * 2 ^ 59
def prefixEnd_479417 : Nat := 4983230072969 + 3 ^ 40 * 479417 * 2
def baseEnd_479417 : Nat := 9117457590246518980841

theorem tailTrace_479417 : CollatzResearch.WordTrace tailWord_479417 prefixEnd_479417 9117457590246518980841 := by
  unfold tailWord_479417
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485774504161561750076505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11657183002774374500051003 17485774504161561750076505)
  ·
    refine ⟨13114330878121171312557379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17485774504161561750076505 13114330878121171312557379)
    ·
      refine ⟨19671496317181756968836069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114330878121171312557379 19671496317181756968836069)
      ·
        refine ⟨3688405559471579431656763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19671496317181756968836069 3688405559471579431656763)
        ·
          refine ⟨5532608339207369147485145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688405559471579431656763 5532608339207369147485145)
          ·
            refine ⟨4149456254405526860613859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532608339207369147485145 4149456254405526860613859)
            ·
              refine ⟨6224184381608290290920789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149456254405526860613859 6224184381608290290920789)
              ·
                refine ⟨9117457590246518980841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6224184381608290290920789 9117457590246518980841)
                ·
                  rfl

theorem cell23_479417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 11].length) (baseStart_479417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479417 prefixEnd_479417 := by exact prefixLift 479417
  have htrace : WordTrace (prefixWord ++ tailWord_479417) baseStart_479417 baseEnd_479417 := by
    simpa [prefixWord, tailWord_479417, baseEnd_479417] using wordTrace_append hprefix tailTrace_479417
  have hstable : (prefixWord ++ tailWord_479417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479417).length < 2 ^ (prefixWord ++ tailWord_479417).sum := by decide
  have hdescent : baseEnd_479417 < baseStart_479417 := by decide
  rcases family_descends (prefixWord ++ tailWord_479417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479424 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_479424 : Nat := 118140960795 + 479424 * 2 ^ 59
def prefixEnd_479424 : Nat := 4983230072969 + 3 ^ 40 * 479424 * 2
def baseEnd_479424 : Nat := 246174949301237485095175

theorem tailTrace_479424 : CollatzResearch.WordTrace tailWord_479424 prefixEnd_479424 246174949301237485095175 := by
  unfold tailWord_479424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743014907568100972790663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11657353210090801297054217 8743014907568100972790663)
  ·
    refine ⟨13114522361352151459185995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8743014907568100972790663 13114522361352151459185995)
    ·
      refine ⟨19671783542028227188778993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114522361352151459185995 19671783542028227188778993)
      ·
        refine ⟨14753837656521170391584245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19671783542028227188778993 14753837656521170391584245)
        ·
          refine ⟨1383172280298859724211023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14753837656521170391584245 1383172280298859724211023)
          ·
            refine ⟨2074758420448289586316535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383172280298859724211023 2074758420448289586316535)
            ·
              refine ⟨3112137630672434379474803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074758420448289586316535 3112137630672434379474803)
              ·
                refine ⟨4668206446008651569212205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112137630672434379474803 4668206446008651569212205)
                ·
                  refine ⟨1750577417253244338454577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4668206446008651569212205 1750577417253244338454577)
                  ·
                    refine ⟨1312933062939933253840933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750577417253244338454577 1312933062939933253840933)
                    ·
                      refine ⟨246174949301237485095175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1312933062939933253840933 246174949301237485095175)
                      ·
                        rfl

theorem cell23_479424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_479424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479424 prefixEnd_479424 := by exact prefixLift 479424
  have htrace : WordTrace (prefixWord ++ tailWord_479424) baseStart_479424 baseEnd_479424 := by
    simpa [prefixWord, tailWord_479424, baseEnd_479424] using wordTrace_append hprefix tailTrace_479424
  have hstable : (prefixWord ++ tailWord_479424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479424).length < 2 ^ (prefixWord ++ tailWord_479424).sum := by decide
  have hdescent : baseEnd_479424 < baseStart_479424 := by decide
  rcases family_descends (prefixWord ++ tailWord_479424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479425 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_479425 : Nat := 118140960795 + 479425 * 2 ^ 59
def prefixEnd_479425 : Nat := 4983230072969 + 3 ^ 40 * 479425 * 2
def baseEnd_479425 : Nat := 82058487593963993727557

theorem tailTrace_479425 : CollatzResearch.WordTrace tailWord_479425 prefixEnd_479425 82058487593963993727557 := by
  unfold tailWord_479425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486066288132579116367729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11657377525421719410911819 17486066288132579116367729)
  ·
    refine ⟨13114549716099434337275797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17486066288132579116367729 13114549716099434337275797)
    ·
      refine ⟨614744517942160984559803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13114549716099434337275797 614744517942160984559803)
      ·
        refine ⟨922116776913241476839705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614744517942160984559803 922116776913241476839705)
        ·
          refine ⟨691587582684931107629779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922116776913241476839705 691587582684931107629779)
          ·
            refine ⟨1037381374027396661444669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691587582684931107629779 1037381374027396661444669)
            ·
              refine ⟨389018015260273748041751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037381374027396661444669 389018015260273748041751)
              ·
                refine ⟨583527022890410622062627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389018015260273748041751 583527022890410622062627)
                ·
                  refine ⟨875290534335615933093941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583527022890410622062627 875290534335615933093941)
                  ·
                    refine ⟨82058487593963993727557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875290534335615933093941 82058487593963993727557)
                    ·
                      rfl

theorem cell23_479425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_479425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479425 prefixEnd_479425 := by exact prefixLift 479425
  have htrace : WordTrace (prefixWord ++ tailWord_479425) baseStart_479425 baseEnd_479425 := by
    simpa [prefixWord, tailWord_479425, baseEnd_479425] using wordTrace_append hprefix tailTrace_479425
  have hstable : (prefixWord ++ tailWord_479425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479425).length < 2 ^ (prefixWord ++ tailWord_479425).sum := by decide
  have hdescent : baseEnd_479425 < baseStart_479425 := by decide
  rcases family_descends (prefixWord ++ tailWord_479425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479438 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_479438 : Nat := 118140960795 + 479438 * 2 ^ 59
def prefixEnd_479438 : Nat := 4983230072969 + 3 ^ 40 * 479438 * 2
def baseEnd_479438 : Nat := 82060712676800143440037

theorem tailTrace_479438 : CollatzResearch.WordTrace tailWord_479438 prefixEnd_479438 82060712676800143440037 := by
  unfold tailWord_479438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185817554635685292073871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11657693624723654891060645 2185817554635685292073871)
  ·
    refine ⟨3278726331953527938110807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185817554635685292073871 3278726331953527938110807)
    ·
      refine ⟨4918089497930291907166211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278726331953527938110807 4918089497930291907166211)
      ·
        refine ⟨7377134246895437860749317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918089497930291907166211 7377134246895437860749317)
        ·
          refine ⟨1383212671292894598890497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7377134246895437860749317 1383212671292894598890497)
          ·
            refine ⟨1037409503469670949167873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383212671292894598890497 1037409503469670949167873)
            ·
              refine ⟨778057127602253211875905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037409503469670949167873 778057127602253211875905)
              ·
                refine ⟨583542845701689908906929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778057127602253211875905 583542845701689908906929)
                ·
                  refine ⟨437657134276267431680197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583542845701689908906929 437657134276267431680197)
                  ·
                    refine ⟨82060712676800143440037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437657134276267431680197 82060712676800143440037)
                    ·
                      rfl

theorem cell23_479438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_479438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479438 prefixEnd_479438 := by exact prefixLift 479438
  have htrace : WordTrace (prefixWord ++ tailWord_479438) baseStart_479438 baseEnd_479438 := by
    simpa [prefixWord, tailWord_479438, baseEnd_479438] using wordTrace_append hprefix tailTrace_479438
  have hstable : (prefixWord ++ tailWord_479438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479438).length < 2 ^ (prefixWord ++ tailWord_479438).sum := by decide
  have hdescent : baseEnd_479438 < baseStart_479438 := by decide
  rcases family_descends (prefixWord ++ tailWord_479438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479461 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_479461 : Nat := 118140960795 + 479461 * 2 ^ 59
def prefixEnd_479461 : Nat := 4983230072969 + 3 ^ 40 * 479461 * 2
def baseEnd_479461 : Nat := 246193948085453840332505

theorem tailTrace_479461 : CollatzResearch.WordTrace tailWord_479461 prefixEnd_479461 246193948085453840332505 := by
  unfold tailWord_479461
  simp only [CollatzResearch.WordTrace]
  refine ⟨17487379316002157264678237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11658252877334771509785491 17487379316002157264678237)
  ·
    refine ⟨6557767243500808974254339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17487379316002157264678237 6557767243500808974254339)
    ·
      refine ⟨9836650865251213461381509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557767243500808974254339 9836650865251213461381509)
      ·
        refine ⟨1844372037234602524009033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9836650865251213461381509 1844372037234602524009033)
        ·
          refine ⟨1383279027925951893006775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844372037234602524009033 1383279027925951893006775)
          ·
            refine ⟨2074918541888927839510163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383279027925951893006775 2074918541888927839510163)
            ·
              refine ⟨3112377812833391759265245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074918541888927839510163 3112377812833391759265245)
              ·
                refine ⟨1167141679812521909724467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112377812833391759265245 1167141679812521909724467)
                ·
                  refine ⟨1750712519718782864586701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167141679812521909724467 1750712519718782864586701)
                  ·
                    refine ⟨656517194894543574220013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1750712519718782864586701 656517194894543574220013)
                    ·
                      refine ⟨246193948085453840332505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 656517194894543574220013 246193948085453840332505)
                      ·
                        rfl

theorem cell23_479461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_479461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479461 prefixEnd_479461 := by exact prefixLift 479461
  have htrace : WordTrace (prefixWord ++ tailWord_479461) baseStart_479461 baseEnd_479461 := by
    simpa [prefixWord, tailWord_479461, baseEnd_479461] using wordTrace_append hprefix tailTrace_479461
  have hstable : (prefixWord ++ tailWord_479461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479461).length < 2 ^ (prefixWord ++ tailWord_479461).sum := by decide
  have hdescent : baseEnd_479461 < baseStart_479461 := by decide
  rcases family_descends (prefixWord ++ tailWord_479461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479495 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_479495 : Nat := 118140960795 + 479495 * 2 ^ 59
def prefixEnd_479495 : Nat := 4983230072969 + 3 ^ 40 * 479495 * 2
def baseEnd_479495 : Nat := 246211406427706707307349

theorem tailTrace_479495 : CollatzResearch.WordTrace tailWord_479495 prefixEnd_479495 246211406427706707307349 := by
  unfold tailWord_479495
  simp only [CollatzResearch.WordTrace]
  refine ⟨17488619397878981071415939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11659079598585987380943959 17488619397878981071415939)
  ·
    refine ⟨26232929096818471607123909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17488619397878981071415939 26232929096818471607123909)
    ·
      refine ⟨4918674205653463426335733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26232929096818471607123909 4918674205653463426335733)
      ·
        refine ⟨461125706780012196218975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4918674205653463426335733 461125706780012196218975)
        ·
          refine ⟨691688560170018294328463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461125706780012196218975 691688560170018294328463)
          ·
            refine ⟨1037532840255027441492695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691688560170018294328463 1037532840255027441492695)
            ·
              refine ⟨1556299260382541162239043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037532840255027441492695 1556299260382541162239043)
              ·
                refine ⟨2334448890573811743358565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556299260382541162239043 2334448890573811743358565)
                ·
                  refine ⟨437709166982589701879731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2334448890573811743358565 437709166982589701879731)
                  ·
                    refine ⟨656563750473884552819597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 437709166982589701879731 656563750473884552819597)
                    ·
                      refine ⟨246211406427706707307349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 656563750473884552819597 246211406427706707307349)
                      ·
                        rfl

theorem cell23_479495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_479495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479495 prefixEnd_479495 := by exact prefixLift 479495
  have htrace : WordTrace (prefixWord ++ tailWord_479495) baseStart_479495 baseEnd_479495 := by
    simpa [prefixWord, tailWord_479495, baseEnd_479495] using wordTrace_append hprefix tailTrace_479495
  have hstable : (prefixWord ++ tailWord_479495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479495).length < 2 ^ (prefixWord ++ tailWord_479495).sum := by decide
  have hdescent : baseEnd_479495 < baseStart_479495 := by decide
  rcases family_descends (prefixWord ++ tailWord_479495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479561 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 5, 2]
def baseStart_479561 : Nat := 118140960795 + 479561 * 2 ^ 59
def prefixEnd_479561 : Nat := 4983230072969 + 3 ^ 40 * 479561 * 2
def baseEnd_479561 : Nat := 246245296150903449082045

theorem tailTrace_479561 : CollatzResearch.WordTrace tailWord_479561 prefixEnd_479561 246245296150903449082045 := by
  unfold tailWord_479561
  simp only [CollatzResearch.WordTrace]
  refine ⟨17491026615639874343318537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11660684410426582895545691 17491026615639874343318537)
  ·
    refine ⟨13118269961729905757488903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17491026615639874343318537 13118269961729905757488903)
    ·
      refine ⟨19677404942594858636233355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13118269961729905757488903 19677404942594858636233355)
      ·
        refine ⟨29516107413892287954350033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677404942594858636233355 29516107413892287954350033)
        ·
          refine ⟨22137080560419215965762525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29516107413892287954350033 22137080560419215965762525)
          ·
            refine ⟨8301405210157205987160947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22137080560419215965762525 8301405210157205987160947)
            ·
              refine ⟨12452107815235808980741421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8301405210157205987160947 12452107815235808980741421)
              ·
                refine ⟨4669540430713428367778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12452107815235808980741421 4669540430713428367778033)
                ·
                  refine ⟨3502155323035071275833525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4669540430713428367778033 3502155323035071275833525)
                  ·
                    refine ⟨328327061534537932109393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3502155323035071275833525 328327061534537932109393)
                    ·
                      refine ⟨246245296150903449082045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328327061534537932109393 246245296150903449082045)
                      ·
                        rfl

theorem cell23_479561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5, 2].length) (baseStart_479561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479561 prefixEnd_479561 := by exact prefixLift 479561
  have htrace : WordTrace (prefixWord ++ tailWord_479561) baseStart_479561 baseEnd_479561 := by
    simpa [prefixWord, tailWord_479561, baseEnd_479561] using wordTrace_append hprefix tailTrace_479561
  have hstable : (prefixWord ++ tailWord_479561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479561).length < 2 ^ (prefixWord ++ tailWord_479561).sum := by decide
  have hdescent : baseEnd_479561 < baseStart_479561 := by decide
  rcases family_descends (prefixWord ++ tailWord_479561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479702 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_479702 : Nat := 118140960795 + 479702 * 2 ^ 59
def prefixEnd_479702 : Nat := 4983230072969 + 3 ^ 40 * 479702 * 2
def baseEnd_479702 : Nat := 246317696923187397418897

theorem tailTrace_479702 : CollatzResearch.WordTrace tailWord_479702 prefixEnd_479702 246317696923187397418897 := by
  unfold tailWord_479702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093510581758065964012585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11664112872086036949467573 1093510581758065964012585)
  ·
    refine ⟨820132936318549473009439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1093510581758065964012585 820132936318549473009439)
    ·
      refine ⟨1230199404477824209514159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 820132936318549473009439 1230199404477824209514159)
      ·
        refine ⟨1845299106716736314271239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230199404477824209514159 1845299106716736314271239)
        ·
          refine ⟨2767948660075104471406859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845299106716736314271239 2767948660075104471406859)
          ·
            refine ⟨4151922990112656707110289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767948660075104471406859 4151922990112656707110289)
            ·
              refine ⟨3113942242584492530332717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4151922990112656707110289 3113942242584492530332717)
              ·
                refine ⟨1167728340969184698874769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3113942242584492530332717 1167728340969184698874769)
                ·
                  refine ⟨875796255726888524156077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167728340969184698874769 875796255726888524156077)
                  ·
                    refine ⟨328423595897583196558529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875796255726888524156077 328423595897583196558529)
                    ·
                      refine ⟨246317696923187397418897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328423595897583196558529 246317696923187397418897)
                      ·
                        rfl

theorem cell23_479702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_479702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479702 prefixEnd_479702 := by exact prefixLift 479702
  have htrace : WordTrace (prefixWord ++ tailWord_479702) baseStart_479702 baseEnd_479702 := by
    simpa [prefixWord, tailWord_479702, baseEnd_479702] using wordTrace_append hprefix tailTrace_479702
  have hstable : (prefixWord ++ tailWord_479702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479702).length < 2 ^ (prefixWord ++ tailWord_479702).sum := by decide
  have hdescent : baseEnd_479702 < baseStart_479702 := by decide
  rcases family_descends (prefixWord ++ tailWord_479702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479725 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_479725 : Nat := 118140960795 + 479725 * 2 ^ 59
def prefixEnd_479725 : Nat := 4983230072969 + 3 ^ 40 * 479725 * 2
def baseEnd_479725 : Nat := 82109835659413602477097

theorem tailTrace_479725 : CollatzResearch.WordTrace tailWord_479725 prefixEnd_479725 82109835659413602477097 := by
  unfold tailWord_479725
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497008187045730352288629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11664672124697153568192419 17497008187045730352288629)
  ·
    refine ⟨1640344517535537220527059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17497008187045730352288629 1640344517535537220527059)
    ·
      refine ⟨2460516776303305830790589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640344517535537220527059 2460516776303305830790589)
      ·
        refine ⟨922693791113739686546471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2460516776303305830790589 922693791113739686546471)
        ·
          refine ⟨1384040686670609529819707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922693791113739686546471 1384040686670609529819707)
          ·
            refine ⟨2076061030005914294729561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384040686670609529819707 2076061030005914294729561)
            ·
              refine ⟨1557045772504435721047171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076061030005914294729561 1557045772504435721047171)
              ·
                refine ⟨2335568658756653581570757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557045772504435721047171 2335568658756653581570757)
                ·
                  refine ⟨437919123516872546544517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335568658756653581570757 437919123516872546544517)
                  ·
                    refine ⟨82109835659413602477097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437919123516872546544517 82109835659413602477097)
                    ·
                      rfl

theorem cell23_479725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_479725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479725 prefixEnd_479725 := by exact prefixLift 479725
  have htrace : WordTrace (prefixWord ++ tailWord_479725) baseStart_479725 baseEnd_479725 := by
    simpa [prefixWord, tailWord_479725, baseEnd_479725] using wordTrace_append hprefix tailTrace_479725
  have hstable : (prefixWord ++ tailWord_479725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479725).length < 2 ^ (prefixWord ++ tailWord_479725).sum := by decide
  have hdescent : baseEnd_479725 < baseStart_479725 := by decide
  rcases family_descends (prefixWord ++ tailWord_479725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479741 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_479741 : Nat := 118140960795 + 479741 * 2 ^ 59
def prefixEnd_479741 : Nat := 4983230072969 + 3 ^ 40 * 479741 * 2
def baseEnd_479741 : Nat := 246337722668712744831217

theorem tailTrace_479741 : CollatzResearch.WordTrace tailWord_479741 prefixEnd_479741 246337722668712744831217 := by
  unfold tailWord_479741
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497591754987765084871077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11665061169991843389914051 17497591754987765084871077)
  ·
    refine ⟨3280798454060205953413327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17497591754987765084871077 3280798454060205953413327)
    ·
      refine ⟨4921197681090308930119991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280798454060205953413327 4921197681090308930119991)
      ·
        refine ⟨7381796521635463395179987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921197681090308930119991 7381796521635463395179987)
        ·
          refine ⟨11072694782453195092769981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381796521635463395179987 11072694782453195092769981)
          ·
            refine ⟨4152260543419948159788743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11072694782453195092769981 4152260543419948159788743)
            ·
              refine ⟨6228390815129922239683115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152260543419948159788743 6228390815129922239683115)
              ·
                refine ⟨9342586222694883359524673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228390815129922239683115 9342586222694883359524673)
                ·
                  refine ⟨7006939667021162519643505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342586222694883359524673 7006939667021162519643505)
                  ·
                    refine ⟨5255204750265871889732629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7006939667021162519643505 5255204750265871889732629)
                    ·
                      refine ⟨246337722668712744831217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5255204750265871889732629 246337722668712744831217)
                      ·
                        rfl

theorem cell23_479741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_479741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479741 prefixEnd_479741 := by exact prefixLift 479741
  have htrace : WordTrace (prefixWord ++ tailWord_479741) baseStart_479741 baseEnd_479741 := by
    simpa [prefixWord, tailWord_479741, baseEnd_479741] using wordTrace_append hprefix tailTrace_479741
  have hstable : (prefixWord ++ tailWord_479741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479741).length < 2 ^ (prefixWord ++ tailWord_479741).sum := by decide
  have hdescent : baseEnd_479741 < baseStart_479741 := by decide
  rcases family_descends (prefixWord ++ tailWord_479741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479761 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_479761 : Nat := 118140960795 + 479761 * 2 ^ 59
def prefixEnd_479761 : Nat := 4983230072969 + 3 ^ 40 * 479761 * 2
def baseEnd_479761 : Nat := 246347992281802666581125

theorem tailTrace_479761 : CollatzResearch.WordTrace tailWord_479761 prefixEnd_479761 246347992281802666581125 := by
  unfold tailWord_479761
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498321214915308500599137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11665547476610205667066091 17498321214915308500599137)
  ·
    refine ⟨13123740911186481375449353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17498321214915308500599137 13123740911186481375449353)
    ·
      refine ⟨9842805683389861031587015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123740911186481375449353 9842805683389861031587015)
      ·
        refine ⟨14764208525084791547380523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842805683389861031587015 14764208525084791547380523)
        ·
          refine ⟨22146312787627187321070785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764208525084791547380523 22146312787627187321070785)
          ·
            refine ⟨16609734590720390490803089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22146312787627187321070785 16609734590720390490803089)
            ·
              refine ⟨12457300943040292868102317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16609734590720390490803089 12457300943040292868102317)
              ·
                refine ⟨4671487853640109825538369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12457300943040292868102317 4671487853640109825538369)
                ·
                  refine ⟨3503615890230082369153777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671487853640109825538369 3503615890230082369153777)
                  ·
                    refine ⟨2627711917672561776865333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503615890230082369153777 2627711917672561776865333)
                    ·
                      refine ⟨246347992281802666581125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2627711917672561776865333 246347992281802666581125)
                      ·
                        rfl

theorem cell23_479761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_479761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479761 prefixEnd_479761 := by exact prefixLift 479761
  have htrace : WordTrace (prefixWord ++ tailWord_479761) baseStart_479761 baseEnd_479761 := by
    simpa [prefixWord, tailWord_479761, baseEnd_479761] using wordTrace_append hprefix tailTrace_479761
  have hstable : (prefixWord ++ tailWord_479761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479761).length < 2 ^ (prefixWord ++ tailWord_479761).sum := by decide
  have hdescent : baseEnd_479761 < baseStart_479761 := by decide
  rcases family_descends (prefixWord ++ tailWord_479761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479771 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_479771 : Nat := 118140960795 + 479771 * 2 ^ 59
def prefixEnd_479771 : Nat := 4983230072969 + 3 ^ 40 * 479771 * 2
def baseEnd_479771 : Nat := 246353127088347627456079

theorem tailTrace_479771 : CollatzResearch.WordTrace tailWord_479771 prefixEnd_479771 246353127088347627456079 := by
  unfold tailWord_479771
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498685944879080208463167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11665790629919386805642111 17498685944879080208463167)
  ·
    refine ⟨26248028917318620312694751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17498685944879080208463167 26248028917318620312694751)
    ·
      refine ⟨39372043375977930469042127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26248028917318620312694751 39372043375977930469042127)
      ·
        refine ⟨59058065063966895703563191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39372043375977930469042127 59058065063966895703563191)
        ·
          refine ⟨88587097595950343555344787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59058065063966895703563191 88587097595950343555344787)
          ·
            refine ⟨132880646393925515333017181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88587097595950343555344787 132880646393925515333017181)
            ·
              refine ⟨49830242397722068249881443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132880646393925515333017181 49830242397722068249881443)
              ·
                refine ⟨74745363596583102374822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49830242397722068249881443 74745363596583102374822165)
                ·
                  refine ⟨3503688918589832923819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74745363596583102374822165 3503688918589832923819789)
                  ·
                    refine ⟨1313883344471187346432421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3503688918589832923819789 1313883344471187346432421)
                    ·
                      refine ⟨246353127088347627456079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1313883344471187346432421 246353127088347627456079)
                      ·
                        rfl

theorem cell23_479771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_479771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479771 prefixEnd_479771 := by exact prefixLift 479771
  have htrace : WordTrace (prefixWord ++ tailWord_479771) baseStart_479771 baseEnd_479771 := by
    simpa [prefixWord, tailWord_479771, baseEnd_479771] using wordTrace_append hprefix tailTrace_479771
  have hstable : (prefixWord ++ tailWord_479771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479771).length < 2 ^ (prefixWord ++ tailWord_479771).sum := by decide
  have hdescent : baseEnd_479771 < baseStart_479771 := by decide
  rcases family_descends (prefixWord ++ tailWord_479771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479783 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_479783 : Nat := 118140960795 + 479783 * 2 ^ 59
def prefixEnd_479783 : Nat := 4983230072969 + 3 ^ 40 * 479783 * 2
def baseEnd_479783 : Nat := 246359288856201580506025

theorem tailTrace_479783 : CollatzResearch.WordTrace tailWord_479783 prefixEnd_479783 246359288856201580506025 := by
  unfold tailWord_479783
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499123620835606257900003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11666082413890404171933335 17499123620835606257900003)
  ·
    refine ⟨26248685431253409386850005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17499123620835606257900003 26248685431253409386850005)
    ·
      refine ⟨615203564795001782504297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26248685431253409386850005 615203564795001782504297)
      ·
        refine ⟨461402673596251336878223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615203564795001782504297 461402673596251336878223)
        ·
          refine ⟨692104010394377005317335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461402673596251336878223 692104010394377005317335)
          ·
            refine ⟨1038156015591565507976003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692104010394377005317335 1038156015591565507976003)
            ·
              refine ⟨1557234023387348261964005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038156015591565507976003 1557234023387348261964005)
              ·
                refine ⟨291981379385127799118251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557234023387348261964005 291981379385127799118251)
                ·
                  refine ⟨437972069077691698677377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291981379385127799118251 437972069077691698677377)
                  ·
                    refine ⟨328479051808268774008033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437972069077691698677377 328479051808268774008033)
                    ·
                      refine ⟨246359288856201580506025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328479051808268774008033 246359288856201580506025)
                      ·
                        rfl

theorem cell23_479783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_479783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479783 prefixEnd_479783 := by exact prefixLift 479783
  have htrace : WordTrace (prefixWord ++ tailWord_479783) baseStart_479783 baseEnd_479783 := by
    simpa [prefixWord, tailWord_479783, baseEnd_479783] using wordTrace_append hprefix tailTrace_479783
  have hstable : (prefixWord ++ tailWord_479783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479783).length < 2 ^ (prefixWord ++ tailWord_479783).sum := by decide
  have hdescent : baseEnd_479783 < baseStart_479783 := by decide
  rcases family_descends (prefixWord ++ tailWord_479783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479789 : List Nat := [1, 5, 4, 1, 1, 2, 1, 8]
def baseStart_479789 : Nat := 118140960795 + 479789 * 2 ^ 59
def prefixEnd_479789 : Nat := 4983230072969 + 3 ^ 40 * 479789 * 2
def baseEnd_479789 : Nat := 9124532212597353964111

theorem tailTrace_479789 : CollatzResearch.WordTrace tailWord_479789 prefixEnd_479789 9124532212597353964111 := by
  unfold tailWord_479789
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499342458813869282618421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11666228305875912855078947 17499342458813869282618421)
  ·
    refine ⟨1640563355513800245245477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17499342458813869282618421 1640563355513800245245477)
    ·
      refine ⟨307605629158837545983527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1640563355513800245245477 307605629158837545983527)
      ·
        refine ⟨461408443738256318975291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307605629158837545983527 461408443738256318975291)
        ·
          refine ⟨692112665607384478462937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461408443738256318975291 692112665607384478462937)
          ·
            refine ⟨519084499205538358847203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692112665607384478462937 519084499205538358847203)
            ·
              refine ⟨778626748808307538270805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519084499205538358847203 778626748808307538270805)
              ·
                refine ⟨9124532212597353964111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 778626748808307538270805 9124532212597353964111)
                ·
                  rfl

theorem cell23_479789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 8].length) (baseStart_479789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479789 prefixEnd_479789 := by exact prefixLift 479789
  have htrace : WordTrace (prefixWord ++ tailWord_479789) baseStart_479789 baseEnd_479789 := by
    simpa [prefixWord, tailWord_479789, baseEnd_479789] using wordTrace_append hprefix tailTrace_479789
  have hstable : (prefixWord ++ tailWord_479789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479789).length < 2 ^ (prefixWord ++ tailWord_479789).sum := by decide
  have hdescent : baseEnd_479789 < baseStart_479789 := by decide
  rcases family_descends (prefixWord ++ tailWord_479789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479845 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 7]
def baseStart_479845 : Nat := 118140960795 + 479845 * 2 ^ 59
def prefixEnd_479845 : Nat := 4983230072969 + 3 ^ 40 * 479845 * 2
def baseEnd_479845 : Nat := 27376791628531148658971

theorem tailTrace_479845 : CollatzResearch.WordTrace tailWord_479845 prefixEnd_479845 27376791628531148658971 := by
  unfold tailWord_479845
  simp only [CollatzResearch.WordTrace]
  refine ⟨17501384946610990846656989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11667589964407327231104659 17501384946610990846656989)
  ·
    refine ⟨6563019354979121567496371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17501384946610990846656989 6563019354979121567496371)
    ·
      refine ⟨9844529032468682351244557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563019354979121567496371 9844529032468682351244557)
      ·
        refine ⟨3691698387175755881716709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9844529032468682351244557 3691698387175755881716709)
        ·
          refine ⟨692193447595454227821883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3691698387175755881716709 692193447595454227821883)
          ·
            refine ⟨1038290171393181341732825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692193447595454227821883 1038290171393181341732825)
            ·
              refine ⟨778717628544886006299619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038290171393181341732825 778717628544886006299619)
              ·
                refine ⟨1168076442817329009449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778717628544886006299619 1168076442817329009449429)
                ·
                  refine ⟨27376791628531148658971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1168076442817329009449429 27376791628531148658971)
                  ·
                    rfl

theorem cell23_479845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_479845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479845 prefixEnd_479845 := by exact prefixLift 479845
  have htrace : WordTrace (prefixWord ++ tailWord_479845) baseStart_479845 baseEnd_479845 := by
    simpa [prefixWord, tailWord_479845, baseEnd_479845] using wordTrace_append hprefix tailTrace_479845
  have hstable : (prefixWord ++ tailWord_479845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479845).length < 2 ^ (prefixWord ++ tailWord_479845).sum := by decide
  have hdescent : baseEnd_479845 < baseStart_479845 := by decide
  rcases family_descends (prefixWord ++ tailWord_479845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479856 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2]
def baseStart_479856 : Nat := 118140960795 + 479856 * 2 ^ 59
def prefixEnd_479856 : Nat := 4983230072969 + 3 ^ 40 * 479856 * 2
def baseEnd_479856 : Nat := 246396772943979794893189

theorem tailTrace_479856 : CollatzResearch.WordTrace tailWord_479856 prefixEnd_479856 246396772943979794893189 := by
  unfold tailWord_479856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750893074785569862653711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11667857433047426483538281 8750893074785569862653711)
  ·
    refine ⟨13126339612178354793980567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750893074785569862653711 13126339612178354793980567)
    ·
      refine ⟨19689509418267532190970851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13126339612178354793980567 19689509418267532190970851)
      ·
        refine ⟨29534264127401298286456277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19689509418267532190970851 29534264127401298286456277)
        ·
          refine ⟨692209315485967928588819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29534264127401298286456277 692209315485967928588819)
          ·
            refine ⟨1038313973228951892883229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692209315485967928588819 1038313973228951892883229)
            ·
              refine ⟨389367739960856959831211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038313973228951892883229 389367739960856959831211)
              ·
                refine ⟨584051609941285439746817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389367739960856959831211 584051609941285439746817)
                ·
                  refine ⟨438038707455964079810113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584051609941285439746817 438038707455964079810113)
                  ·
                    refine ⟨328529030591973059857585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438038707455964079810113 328529030591973059857585)
                    ·
                      refine ⟨246396772943979794893189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328529030591973059857585 246396772943979794893189)
                      ·
                        rfl

theorem cell23_479856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2].length) (baseStart_479856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479856 prefixEnd_479856 := by exact prefixLift 479856
  have htrace : WordTrace (prefixWord ++ tailWord_479856) baseStart_479856 baseEnd_479856 := by
    simpa [prefixWord, tailWord_479856, baseEnd_479856] using wordTrace_append hprefix tailTrace_479856
  have hstable : (prefixWord ++ tailWord_479856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479856).length < 2 ^ (prefixWord ++ tailWord_479856).sum := by decide
  have hdescent : baseEnd_479856 < baseStart_479856 := by decide
  rcases family_descends (prefixWord ++ tailWord_479856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479892 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_479892 : Nat := 118140960795 + 479892 * 2 ^ 59
def prefixEnd_479892 : Nat := 4983230072969 + 3 ^ 40 * 479892 * 2
def baseEnd_479892 : Nat := 82138419415847218014341

theorem tailTrace_479892 : CollatzResearch.WordTrace tailWord_479892 prefixEnd_479892 82138419415847218014341 := by
  unfold tailWord_479892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751549588720358936808965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11668732784960478582411953 8751549588720358936808965)
  ·
    refine ⟨1640915547885067300651681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8751549588720358936808965 1640915547885067300651681)
    ·
      refine ⟨1230686660913800475488761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640915547885067300651681 1230686660913800475488761)
      ·
        refine ⟨923014995685350356616571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230686660913800475488761 923014995685350356616571)
        ·
          refine ⟨1384522493528025534924857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923014995685350356616571 1384522493528025534924857)
          ·
            refine ⟨1038391870146019151193643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384522493528025534924857 1038391870146019151193643)
            ·
              refine ⟨1557587805219028726790465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038391870146019151193643 1557587805219028726790465)
              ·
                refine ⟨1168190853914271545092849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557587805219028726790465 1168190853914271545092849)
                ·
                  refine ⟨876143140435703658819637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168190853914271545092849 876143140435703658819637)
                  ·
                    refine ⟨82138419415847218014341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 876143140435703658819637 82138419415847218014341)
                    ·
                      rfl

theorem cell23_479892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_479892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479892 prefixEnd_479892 := by exact prefixLift 479892
  have htrace : WordTrace (prefixWord ++ tailWord_479892) baseStart_479892 baseEnd_479892 := by
    simpa [prefixWord, tailWord_479892, baseEnd_479892] using wordTrace_append hprefix tailTrace_479892
  have hstable : (prefixWord ++ tailWord_479892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479892).length < 2 ^ (prefixWord ++ tailWord_479892).sum := by decide
  have hdescent : baseEnd_479892 < baseStart_479892 := by decide
  rcases family_descends (prefixWord ++ tailWord_479892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479895 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_479895 : Nat := 118140960795 + 479895 * 2 ^ 59
def prefixEnd_479895 : Nat := 4983230072969 + 3 ^ 40 * 479895 * 2
def baseEnd_479895 : Nat := 246416798689505142305509

theorem tailTrace_479895 : CollatzResearch.WordTrace tailWord_479895 prefixEnd_479895 246416798689505142305509 := by
  unfold tailWord_479895
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503208596429849385977139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11668805730953232923984759 17503208596429849385977139)
  ·
    refine ⟨26254812894644774078965709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503208596429849385977139 26254812894644774078965709)
    ·
      refine ⟨9845554835491790279612141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26254812894644774078965709 9845554835491790279612141)
      ·
        refine ⟨3692083063309421354854553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9845554835491790279612141 3692083063309421354854553)
        ·
          refine ⟨2769062297482066016140915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692083063309421354854553 2769062297482066016140915)
          ·
            refine ⟨4153593446223099024211373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769062297482066016140915 4153593446223099024211373)
            ·
              refine ⟨1557597542333662134079265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153593446223099024211373 1557597542333662134079265)
              ·
                refine ⟨1168198156750246600559449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1557597542333662134079265 1168198156750246600559449)
                ·
                  refine ⟨876148617562684950419587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168198156750246600559449 876148617562684950419587)
                  ·
                    refine ⟨1314222926344027425629381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876148617562684950419587 1314222926344027425629381)
                    ·
                      refine ⟨246416798689505142305509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1314222926344027425629381 246416798689505142305509)
                      ·
                        rfl

theorem cell23_479895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_479895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479895 prefixEnd_479895 := by exact prefixLift 479895
  have htrace : WordTrace (prefixWord ++ tailWord_479895) baseStart_479895 baseEnd_479895 := by
    simpa [prefixWord, tailWord_479895, baseEnd_479895] using wordTrace_append hprefix tailTrace_479895
  have hstable : (prefixWord ++ tailWord_479895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479895).length < 2 ^ (prefixWord ++ tailWord_479895).sum := by decide
  have hdescent : baseEnd_479895 < baseStart_479895 := by decide
  rcases family_descends (prefixWord ++ tailWord_479895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479932 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_479932 : Nat := 118140960795 + 479932 * 2 ^ 59
def prefixEnd_479932 : Nat := 4983230072969 + 3 ^ 40 * 479932 * 2
def baseEnd_479932 : Nat := 246435797473721497542839

theorem tailTrace_479932 : CollatzResearch.WordTrace tailWord_479932 prefixEnd_479932 246435797473721497542839 := by
  unfold tailWord_479932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752279048647902352537025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11669705398197203136716033 8752279048647902352537025)
  ·
    refine ⟨6564209286485926764402769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8752279048647902352537025 6564209286485926764402769)
    ·
      refine ⟨4923156964864445073302077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6564209286485926764402769 4923156964864445073302077)
      ·
        refine ⟨1846183861824166902488279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4923156964864445073302077 1846183861824166902488279)
        ·
          refine ⟨2769275792736250353732419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846183861824166902488279 2769275792736250353732419)
          ·
            refine ⟨4153913689104375530598629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769275792736250353732419 4153913689104375530598629)
            ·
              refine ⟨778858816707070411987243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4153913689104375530598629 778858816707070411987243)
              ·
                refine ⟨1168288225060605617980865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778858816707070411987243 1168288225060605617980865)
                ·
                  refine ⟨876216168795454213485649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168288225060605617980865 876216168795454213485649)
                  ·
                    refine ⟨657162126596590660114237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876216168795454213485649 657162126596590660114237)
                    ·
                      refine ⟨246435797473721497542839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 657162126596590660114237 246435797473721497542839)
                      ·
                        rfl

theorem cell23_479932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_479932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479932 prefixEnd_479932 := by exact prefixLift 479932
  have htrace : WordTrace (prefixWord ++ tailWord_479932) baseStart_479932 baseEnd_479932 := by
    simpa [prefixWord, tailWord_479932, baseEnd_479932] using wordTrace_append hprefix tailTrace_479932
  have hstable : (prefixWord ++ tailWord_479932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479932).length < 2 ^ (prefixWord ++ tailWord_479932).sum := by decide
  have hdescent : baseEnd_479932 < baseStart_479932 := by decide
  rcases family_descends (prefixWord ++ tailWord_479932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479956 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_479956 : Nat := 118140960795 + 479956 * 2 ^ 59
def prefixEnd_479956 : Nat := 4983230072969 + 3 ^ 40 * 479956 * 2
def baseEnd_479956 : Nat := 82149373669809801214243

theorem tailTrace_479956 : CollatzResearch.WordTrace tailWord_479956 prefixEnd_479956 82149373669809801214243 := by
  unfold tailWord_479956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752716724604428401973861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11670288966139237869298481 8752716724604428401973861)
  ·
    refine ⟨1641134385863330325370099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8752716724604428401973861 1641134385863330325370099)
    ·
      refine ⟨2461701578794995488055149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1641134385863330325370099 2461701578794995488055149)
      ·
        refine ⟨923138092048123308020681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2461701578794995488055149 923138092048123308020681)
        ·
          refine ⟨692353569036092481015511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923138092048123308020681 692353569036092481015511)
          ·
            refine ⟨1038530353554138721523267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692353569036092481015511 1038530353554138721523267)
            ·
              refine ⟨1557795530331208082284901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038530353554138721523267 1557795530331208082284901)
              ·
                refine ⟨292086661937101515428419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557795530331208082284901 292086661937101515428419)
                ·
                  refine ⟨438129992905652273142629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292086661937101515428419 438129992905652273142629)
                  ·
                    refine ⟨82149373669809801214243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438129992905652273142629 82149373669809801214243)
                    ·
                      rfl

theorem cell23_479956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_479956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479956 prefixEnd_479956 := by exact prefixLift 479956
  have htrace : WordTrace (prefixWord ++ tailWord_479956) baseStart_479956 baseEnd_479956 := by
    simpa [prefixWord, tailWord_479956, baseEnd_479956] using wordTrace_append hprefix tailTrace_479956
  have hstable : (prefixWord ++ tailWord_479956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479956).length < 2 ^ (prefixWord ++ tailWord_479956).sum := by decide
  have hdescent : baseEnd_479956 < baseStart_479956 := by decide
  rcases family_descends (prefixWord ++ tailWord_479956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479962 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_479962 : Nat := 118140960795 + 479962 * 2 ^ 59
def prefixEnd_479962 : Nat := 4983230072969 + 3 ^ 40 * 479962 * 2
def baseEnd_479962 : Nat := 246451201893356380167701

theorem tailTrace_479962 : CollatzResearch.WordTrace tailWord_479962 prefixEnd_479962 246451201893356380167701 := by
  unfold tailWord_479962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376413071796779957166535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11670434858124746552444093 4376413071796779957166535)
  ·
    refine ⟨6564619607695169935749803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4376413071796779957166535 6564619607695169935749803)
    ·
      refine ⟨9846929411542754903624705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564619607695169935749803 9846929411542754903624705)
      ·
        refine ⟨7385197058657066177718529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9846929411542754903624705 7385197058657066177718529)
        ·
          refine ⟨5538897793992799633288897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7385197058657066177718529 5538897793992799633288897)
          ·
            refine ⟨4154173345494599724966673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538897793992799633288897 4154173345494599724966673)
            ·
              refine ⟨3115630009120949793725005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154173345494599724966673 3115630009120949793725005)
              ·
                refine ⟨1168361253420356172646877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3115630009120949793725005 1168361253420356172646877)
                ·
                  refine ⟨438135470032633564742579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168361253420356172646877 438135470032633564742579)
                  ·
                    refine ⟨657203205048950347113869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 438135470032633564742579 657203205048950347113869)
                    ·
                      refine ⟨246451201893356380167701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 657203205048950347113869 246451201893356380167701)
                      ·
                        rfl

theorem cell23_479962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_479962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479962 prefixEnd_479962 := by exact prefixLift 479962
  have htrace : WordTrace (prefixWord ++ tailWord_479962) baseStart_479962 baseEnd_479962 := by
    simpa [prefixWord, tailWord_479962, baseEnd_479962] using wordTrace_append hprefix tailTrace_479962
  have hstable : (prefixWord ++ tailWord_479962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479962).length < 2 ^ (prefixWord ++ tailWord_479962).sum := by decide
  have hdescent : baseEnd_479962 < baseStart_479962 := by decide
  rcases family_descends (prefixWord ++ tailWord_479962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479985 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_479985 : Nat := 118140960795 + 479985 * 2 ^ 59
def prefixEnd_479985 : Nat := 4983230072969 + 3 ^ 40 * 479985 * 2
def baseEnd_479985 : Nat := 246463011948409790180095

theorem tailTrace_479985 : CollatzResearch.WordTrace tailWord_479985 prefixEnd_479985 246463011948409790180095 := by
  unfold tailWord_479985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506491166103794756753409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11670994110735863171168939 17506491166103794756753409)
  ·
    refine ⟨13129868374577846067565057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17506491166103794756753409 13129868374577846067565057)
    ·
      refine ⟨9847401280933384550673793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13129868374577846067565057 9847401280933384550673793)
      ·
        refine ⟨7385550960700038413005345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9847401280933384550673793 7385550960700038413005345)
        ·
          refine ⟨5539163220525028809754009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7385550960700038413005345 5539163220525028809754009)
          ·
            refine ⟨4154372415393771607315507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5539163220525028809754009 4154372415393771607315507)
            ·
              refine ⟨6231558623090657410973261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154372415393771607315507 6231558623090657410973261)
              ·
                refine ⟨2336834483658996529114973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231558623090657410973261 2336834483658996529114973)
                ·
                  refine ⟨876312931372123698418115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2336834483658996529114973 876312931372123698418115)
                  ·
                    refine ⟨1314469397058185547627173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 876312931372123698418115 1314469397058185547627173)
                    ·
                      refine ⟨246463011948409790180095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1314469397058185547627173 246463011948409790180095)
                      ·
                        rfl

theorem cell23_479985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_479985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479985 prefixEnd_479985 := by exact prefixLift 479985
  have htrace : WordTrace (prefixWord ++ tailWord_479985) baseStart_479985 baseEnd_479985 := by
    simpa [prefixWord, tailWord_479985, baseEnd_479985] using wordTrace_append hprefix tailTrace_479985
  have hstable : (prefixWord ++ tailWord_479985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479985).length < 2 ^ (prefixWord ++ tailWord_479985).sum := by decide
  have hdescent : baseEnd_479985 < baseStart_479985 := by decide
  rcases family_descends (prefixWord ++ tailWord_479985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_479996 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_479996 : Nat := 118140960795 + 479996 * 2 ^ 59
def prefixEnd_479996 : Nat := 4983230072969 + 3 ^ 40 * 479996 * 2
def baseEnd_479996 : Nat := 246468660235609247142545

theorem tailTrace_479996 : CollatzResearch.WordTrace tailWord_479996 prefixEnd_479996 246468660235609247142545 := by
  unfold tailWord_479996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753446184531971817701921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11671261579375962423602561 8753446184531971817701921)
  ·
    refine ⟨6565084638398978863276441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8753446184531971817701921 6565084638398978863276441)
    ·
      refine ⟨4923813478799234147457331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6565084638398978863276441 4923813478799234147457331)
      ·
        refine ⟨7385720218198851221185997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923813478799234147457331 7385720218198851221185997)
        ·
          refine ⟨2769645081824569207944749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7385720218198851221185997 2769645081824569207944749)
          ·
            refine ⟨1038616905684213452979281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2769645081824569207944749 1038616905684213452979281)
            ·
              refine ⟨778962679263160089734461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038616905684213452979281 778962679263160089734461)
              ·
                refine ⟨292111004723685033650423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778962679263160089734461 292111004723685033650423)
                ·
                  refine ⟨438166507085527550475635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292111004723685033650423 438166507085527550475635)
                  ·
                    refine ⟨657249760628291325713453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 438166507085527550475635 657249760628291325713453)
                    ·
                      refine ⟨246468660235609247142545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 657249760628291325713453 246468660235609247142545)
                      ·
                        rfl

theorem cell23_479996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_479996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_479996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_479996 prefixEnd_479996 := by exact prefixLift 479996
  have htrace : WordTrace (prefixWord ++ tailWord_479996) baseStart_479996 baseEnd_479996 := by
    simpa [prefixWord, tailWord_479996, baseEnd_479996] using wordTrace_append hprefix tailTrace_479996
  have hstable : (prefixWord ++ tailWord_479996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_479996).length < 2 ^ (prefixWord ++ tailWord_479996).sum := by decide
  have hdescent : baseEnd_479996 < baseStart_479996 := by decide
  rcases family_descends (prefixWord ++ tailWord_479996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480019 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 3, 2, 2]
def baseStart_480019 : Nat := 118140960795 + 480019 * 2 ^ 59
def prefixEnd_480019 : Nat := 4983230072969 + 3 ^ 40 * 480019 * 2
def baseEnd_480019 : Nat := 246480470290662657154939

theorem tailTrace_480019 : CollatzResearch.WordTrace tailWord_480019 prefixEnd_480019 246480470290662657154939 := by
  unfold tailWord_480019
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507731247980618563491111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11671820831987079042327407 17507731247980618563491111)
  ·
    refine ⟨26261596871970927845236667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17507731247980618563491111 26261596871970927845236667)
    ·
      refine ⟨39392395307956391767855001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26261596871970927845236667 39392395307956391767855001)
      ·
        refine ⟨29544296480967293825891251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39392395307956391767855001 29544296480967293825891251)
        ·
          refine ⟨44316444721450940738836877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29544296480967293825891251 44316444721450940738836877)
          ·
            refine ⟨16618666770544102777063829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44316444721450940738836877 16618666770544102777063829)
            ·
              refine ⟨779000004869254817674867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16618666770544102777063829 779000004869254817674867)
              ·
                refine ⟨1168500007303882226512301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779000004869254817674867 1168500007303882226512301)
                ·
                  refine ⟨438187502738955834942113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168500007303882226512301 438187502738955834942113)
                  ·
                    refine ⟨328640627054216876206585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438187502738955834942113 328640627054216876206585)
                    ·
                      refine ⟨246480470290662657154939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328640627054216876206585 246480470290662657154939)
                      ·
                        rfl

theorem cell23_480019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2, 2].length) (baseStart_480019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480019 prefixEnd_480019 := by exact prefixLift 480019
  have htrace : WordTrace (prefixWord ++ tailWord_480019) baseStart_480019 baseEnd_480019 := by
    simpa [prefixWord, tailWord_480019, baseEnd_480019] using wordTrace_append hprefix tailTrace_480019
  have hstable : (prefixWord ++ tailWord_480019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480019).length < 2 ^ (prefixWord ++ tailWord_480019).sum := by decide
  have hdescent : baseEnd_480019 < baseStart_480019 := by decide
  rcases family_descends (prefixWord ++ tailWord_480019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480032 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_480032 : Nat := 118140960795 + 480032 * 2 ^ 59
def prefixEnd_480032 : Nat := 4983230072969 + 3 ^ 40 * 480032 * 2
def baseEnd_480032 : Nat := 246487145539171106292379

theorem tailTrace_480032 : CollatzResearch.WordTrace tailWord_480032 prefixEnd_480032 246487145539171106292379 := by
  unfold tailWord_480032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754102698466760891857175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11672136931289014522476233 8754102698466760891857175)
  ·
    refine ⟨13131154047700141337785763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8754102698466760891857175 13131154047700141337785763)
    ·
      refine ⟨19696731071550212006678645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13131154047700141337785763 19696731071550212006678645)
      ·
        refine ⟨1846568537957832375626123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19696731071550212006678645 1846568537957832375626123)
        ·
          refine ⟨2769852806936748563439185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846568537957832375626123 2769852806936748563439185)
          ·
            refine ⟨2077389605202561422579389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769852806936748563439185 2077389605202561422579389)
            ·
              refine ⟨779021101950960533467271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077389605202561422579389 779021101950960533467271)
              ·
                refine ⟨1168531652926440800200907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779021101950960533467271 1168531652926440800200907)
                ·
                  refine ⟨1752797479389661200301361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168531652926440800200907 1752797479389661200301361)
                  ·
                    refine ⟨1314598109542245900226021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752797479389661200301361 1314598109542245900226021)
                    ·
                      refine ⟨246487145539171106292379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1314598109542245900226021 246487145539171106292379)
                      ·
                        rfl

theorem cell23_480032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_480032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480032 prefixEnd_480032 := by exact prefixLift 480032
  have htrace : WordTrace (prefixWord ++ tailWord_480032) baseStart_480032 baseEnd_480032 := by
    simpa [prefixWord, tailWord_480032, baseEnd_480032] using wordTrace_append hprefix tailTrace_480032
  have hstable : (prefixWord ++ tailWord_480032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480032).length < 2 ^ (prefixWord ++ tailWord_480032).sum := by decide
  have hdescent : baseEnd_480032 < baseStart_480032 := by decide
  rcases family_descends (prefixWord ++ tailWord_480032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480053 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_480053 : Nat := 118140960795 + 480053 * 2 ^ 59
def prefixEnd_480053 : Nat := 4983230072969 + 3 ^ 40 * 480053 * 2
def baseEnd_480053 : Nat := 246497928632915524129783

theorem tailTrace_480053 : CollatzResearch.WordTrace tailWord_480053 prefixEnd_480053 246497928632915524129783 := by
  unfold tailWord_480053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508971329857442370228813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11672647553238294913485875 17508971329857442370228813)
  ·
    refine ⟨6565864248696540888835805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17508971329857442370228813 6565864248696540888835805)
    ·
      refine ⟨2462199093261202833313427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6565864248696540888835805 2462199093261202833313427)
      ·
        refine ⟨3693298639891804249970141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462199093261202833313427 3693298639891804249970141)
        ·
          refine ⟨1384986989959426593738803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3693298639891804249970141 1384986989959426593738803)
          ·
            refine ⟨2077480484939139890608205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384986989959426593738803 2077480484939139890608205)
            ·
              refine ⟨779055181852177458978077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2077480484939139890608205 779055181852177458978077)
              ·
                refine ⟨292145693194566547116779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779055181852177458978077 292145693194566547116779)
                ·
                  refine ⟨438218539791849820675169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292145693194566547116779 438218539791849820675169)
                  ·
                    refine ⟨328663904843887365506377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438218539791849820675169 328663904843887365506377)
                    ·
                      refine ⟨246497928632915524129783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328663904843887365506377 246497928632915524129783)
                      ·
                        rfl

theorem cell23_480053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_480053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480053 prefixEnd_480053 := by exact prefixLift 480053
  have htrace : WordTrace (prefixWord ++ tailWord_480053) baseStart_480053 baseEnd_480053 := by
    simpa [prefixWord, tailWord_480053, baseEnd_480053] using wordTrace_append hprefix tailTrace_480053
  have hstable : (prefixWord ++ tailWord_480053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480053).length < 2 ^ (prefixWord ++ tailWord_480053).sum := by decide
  have hdescent : baseEnd_480053 < baseStart_480053 := by decide
  rcases family_descends (prefixWord ++ tailWord_480053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480085 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_480085 : Nat := 118140960795 + 480085 * 2 ^ 59
def prefixEnd_480085 : Nat := 4983230072969 + 3 ^ 40 * 480085 * 2
def baseEnd_480085 : Nat := 82171453337953132976545

theorem tailTrace_480085 : CollatzResearch.WordTrace tailWord_480085 prefixEnd_480085 82171453337953132976545 := by
  unfold tailWord_480085
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510138465741511835393709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673425643827674556929139 17510138465741511835393709)
  ·
    refine ⟨6566301924653066938272641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17510138465741511835393709 6566301924653066938272641)
    ·
      refine ⟨4924726443489800203704481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6566301924653066938272641 4924726443489800203704481)
      ·
        refine ⟨3693544832617350152778361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924726443489800203704481 3693544832617350152778361)
        ·
          refine ⟨2770158624463012614583771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3693544832617350152778361 2770158624463012614583771)
          ·
            refine ⟨4155237936694518921875657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770158624463012614583771 4155237936694518921875657)
            ·
              refine ⟨3116428452520889191406743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155237936694518921875657 3116428452520889191406743)
              ·
                refine ⟨4674642678781333787110115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116428452520889191406743 4674642678781333787110115)
                ·
                  refine ⟨7011964018172000680665173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674642678781333787110115 7011964018172000680665173)
                  ·
                    refine ⟨82171453337953132976545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7011964018172000680665173 82171453337953132976545)
                    ·
                      rfl

theorem cell23_480085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_480085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480085 prefixEnd_480085 := by exact prefixLift 480085
  have htrace : WordTrace (prefixWord ++ tailWord_480085) baseStart_480085 baseEnd_480085 := by
    simpa [prefixWord, tailWord_480085, baseEnd_480085] using wordTrace_append hprefix tailTrace_480085
  have hstable : (prefixWord ++ tailWord_480085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480085).length < 2 ^ (prefixWord ++ tailWord_480085).sum := by decide
  have hdescent : baseEnd_480085 < baseStart_480085 := by decide
  rcases family_descends (prefixWord ++ tailWord_480085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480095 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_480095 : Nat := 118140960795 + 480095 * 2 ^ 59
def prefixEnd_480095 : Nat := 4983230072969 + 3 ^ 40 * 480095 * 2
def baseEnd_480095 : Nat := 246519494820404359804589

theorem tailTrace_480095 : CollatzResearch.WordTrace tailWord_480095 prefixEnd_480095 246519494820404359804589 := by
  unfold tailWord_480095
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510503195705283543257739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673668797136855695505159 17510503195705283543257739)
  ·
    refine ⟨26265754793557925314886609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17510503195705283543257739 26265754793557925314886609)
    ·
      refine ⟨19699316095168443986164957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26265754793557925314886609 19699316095168443986164957)
      ·
        refine ⟨7387243535688166494811859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19699316095168443986164957 7387243535688166494811859)
        ·
          refine ⟨11080865303532249742217789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387243535688166494811859 11080865303532249742217789)
          ·
            refine ⟨4155324488824593653331671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11080865303532249742217789 4155324488824593653331671)
            ·
              refine ⟨6232986733236890479997507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155324488824593653331671 6232986733236890479997507)
              ·
                refine ⟨9349480099855335719996261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232986733236890479997507 9349480099855335719996261)
                ·
                  refine ⟨1753027518722875447499299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9349480099855335719996261 1753027518722875447499299)
                  ·
                    refine ⟨2629541278084313171248949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1753027518722875447499299 2629541278084313171248949)
                    ·
                      refine ⟨246519494820404359804589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2629541278084313171248949 246519494820404359804589)
                      ·
                        rfl

theorem cell23_480095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_480095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480095 prefixEnd_480095 := by exact prefixLift 480095
  have htrace : WordTrace (prefixWord ++ tailWord_480095) baseStart_480095 baseEnd_480095 := by
    simpa [prefixWord, tailWord_480095, baseEnd_480095] using wordTrace_append hprefix tailTrace_480095
  have hstable : (prefixWord ++ tailWord_480095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480095).length < 2 ^ (prefixWord ++ tailWord_480095).sum := by decide
  have hdescent : baseEnd_480095 < baseStart_480095 := by decide
  rcases family_descends (prefixWord ++ tailWord_480095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480105 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_480105 : Nat := 118140960795 + 480105 * 2 ^ 59
def prefixEnd_480105 : Nat := 4983230072969 + 3 ^ 40 * 480105 * 2
def baseEnd_480105 : Nat := 246524629626949320679543

theorem tailTrace_480105 : CollatzResearch.WordTrace tailWord_480105 prefixEnd_480105 246524629626949320679543 := by
  unfold tailWord_480105
  simp only [CollatzResearch.WordTrace]
  refine ⟨17510867925669055251121769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11673911950446036834081179 17510867925669055251121769)
  ·
    refine ⟨13133150944251791438341327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17510867925669055251121769 13133150944251791438341327)
    ·
      refine ⟨19699726416377687157511991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13133150944251791438341327 19699726416377687157511991)
      ·
        refine ⟨29549589624566530736267987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19699726416377687157511991 29549589624566530736267987)
        ·
          refine ⟨44324384436849796104401981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29549589624566530736267987 44324384436849796104401981)
          ·
            refine ⟨16621644163818673539150743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44324384436849796104401981 16621644163818673539150743)
            ·
              refine ⟨24932466245728010308726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16621644163818673539150743 24932466245728010308726115)
              ·
                refine ⟨37398699368592015463089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24932466245728010308726115 37398699368592015463089173)
                ·
                  refine ⟨1753064032902750724832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37398699368592015463089173 1753064032902750724832305)
                  ·
                    refine ⟨1314798024677063043624229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753064032902750724832305 1314798024677063043624229)
                    ·
                      refine ⟨246524629626949320679543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1314798024677063043624229 246524629626949320679543)
                      ·
                        rfl

theorem cell23_480105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_480105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480105 prefixEnd_480105 := by exact prefixLift 480105
  have htrace : WordTrace (prefixWord ++ tailWord_480105) baseStart_480105 baseEnd_480105 := by
    simpa [prefixWord, tailWord_480105, baseEnd_480105] using wordTrace_append hprefix tailTrace_480105
  have hstable : (prefixWord ++ tailWord_480105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480105).length < 2 ^ (prefixWord ++ tailWord_480105).sum := by decide
  have hdescent : baseEnd_480105 < baseStart_480105 := by decide
  rcases family_descends (prefixWord ++ tailWord_480105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480125 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_480125 : Nat := 118140960795 + 480125 * 2 ^ 59
def prefixEnd_480125 : Nat := 4983230072969 + 3 ^ 40 * 480125 * 2
def baseEnd_480125 : Nat := 246534899240039242429451

theorem tailTrace_480125 : CollatzResearch.WordTrace tailWord_480125 prefixEnd_480125 246534899240039242429451 := by
  unfold tailWord_480125
  simp only [CollatzResearch.WordTrace]
  refine ⟨17511597385596598666849829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11674398257064399111233219 17511597385596598666849829)
  ·
    refine ⟨3283424509799362250034343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17511597385596598666849829 3283424509799362250034343)
    ·
      refine ⟨4925136764699043375051515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3283424509799362250034343 4925136764699043375051515)
      ·
        refine ⟨7387705147048565062577273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925136764699043375051515 7387705147048565062577273)
        ·
          refine ⟨5540778860286423796932955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7387705147048565062577273 5540778860286423796932955)
          ·
            refine ⟨8311168290429635695399433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540778860286423796932955 8311168290429635695399433)
            ·
              refine ⟨6233376217822226771549575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8311168290429635695399433 6233376217822226771549575)
              ·
                refine ⟨9350064326733340157324363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233376217822226771549575 9350064326733340157324363)
                ·
                  refine ⟨14025096490100010235986545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350064326733340157324363 14025096490100010235986545)
                  ·
                    refine ⟨10518822367575007676989909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14025096490100010235986545 10518822367575007676989909)
                    ·
                      refine ⟨246534899240039242429451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10518822367575007676989909 246534899240039242429451)
                      ·
                        rfl

theorem cell23_480125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_480125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480125 prefixEnd_480125 := by exact prefixLift 480125
  have htrace : WordTrace (prefixWord ++ tailWord_480125) baseStart_480125 baseEnd_480125 := by
    simpa [prefixWord, tailWord_480125, baseEnd_480125] using wordTrace_append hprefix tailTrace_480125
  have hstable : (prefixWord ++ tailWord_480125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480125).length < 2 ^ (prefixWord ++ tailWord_480125).sum := by decide
  have hdescent : baseEnd_480125 < baseStart_480125 := by decide
  rcases family_descends (prefixWord ++ tailWord_480125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480145 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_480145 : Nat := 118140960795 + 480145 * 2 ^ 59
def prefixEnd_480145 : Nat := 4983230072969 + 3 ^ 40 * 480145 * 2
def baseEnd_480145 : Nat := 82181722951043054726453

theorem tailTrace_480145 : CollatzResearch.WordTrace tailWord_480145 prefixEnd_480145 82181722951043054726453 := by
  unfold tailWord_480145
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512326845524142082577889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11674884563682761388385259 17512326845524142082577889)
  ·
    refine ⟨13134245134143106561933417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17512326845524142082577889 13134245134143106561933417)
    ·
      refine ⟨9850683850607329921450063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13134245134143106561933417 9850683850607329921450063)
      ·
        refine ⟨14776025775910994882175095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9850683850607329921450063 14776025775910994882175095)
        ·
          refine ⟨22164038663866492323262643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776025775910994882175095 22164038663866492323262643)
          ·
            refine ⟨33246057995799738484893965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22164038663866492323262643 33246057995799738484893965)
            ·
              refine ⟨12467271748424901931835237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33246057995799738484893965 12467271748424901931835237)
              ·
                refine ⟨2337613452829669112219107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12467271748424901931835237 2337613452829669112219107)
                ·
                  refine ⟨3506420179244503668328661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337613452829669112219107 3506420179244503668328661)
                  ·
                    refine ⟨82181722951043054726453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3506420179244503668328661 82181722951043054726453)
                    ·
                      rfl

theorem cell23_480145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_480145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480145 prefixEnd_480145 := by exact prefixLift 480145
  have htrace : WordTrace (prefixWord ++ tailWord_480145) baseStart_480145 baseEnd_480145 := by
    simpa [prefixWord, tailWord_480145, baseEnd_480145] using wordTrace_append hprefix tailTrace_480145
  have hstable : (prefixWord ++ tailWord_480145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480145).length < 2 ^ (prefixWord ++ tailWord_480145).sum := by decide
  have hdescent : baseEnd_480145 < baseStart_480145 := by decide
  rcases family_descends (prefixWord ++ tailWord_480145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480199 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_480199 : Nat := 118140960795 + 480199 * 2 ^ 59
def prefixEnd_480199 : Nat := 4983230072969 + 3 ^ 40 * 480199 * 2
def baseEnd_480199 : Nat := 246572896808471952904111

theorem tailTrace_480199 : CollatzResearch.WordTrace tailWord_480199 prefixEnd_480199 246572896808471952904111 := by
  unfold tailWord_480199
  simp only [CollatzResearch.WordTrace]
  refine ⟨17514296387328509305043651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11676197591552339536695767 17514296387328509305043651)
  ·
    refine ⟨26271444580992763957565477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17514296387328509305043651 26271444580992763957565477)
    ·
      refine ⟨4925895858936143242043527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26271444580992763957565477 4925895858936143242043527)
      ·
        refine ⟨7388843788404214863065291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925895858936143242043527 7388843788404214863065291)
        ·
          refine ⟨11083265682606322294597937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388843788404214863065291 11083265682606322294597937)
          ·
            refine ⟨8312449261954741720948453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11083265682606322294597937 8312449261954741720948453)
            ·
              refine ⟨1558584236616514072677835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8312449261954741720948453 1558584236616514072677835)
              ·
                refine ⟨2337876354924771109016753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558584236616514072677835 2337876354924771109016753)
                ·
                  refine ⟨1753407266193578331762565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2337876354924771109016753 1753407266193578331762565)
                  ·
                    refine ⟨328763862411295937205481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753407266193578331762565 328763862411295937205481)
                    ·
                      refine ⟨246572896808471952904111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328763862411295937205481 246572896808471952904111)
                      ·
                        rfl

theorem cell23_480199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_480199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480199 prefixEnd_480199 := by exact prefixLift 480199
  have htrace : WordTrace (prefixWord ++ tailWord_480199) baseStart_480199 baseEnd_480199 := by
    simpa [prefixWord, tailWord_480199, baseEnd_480199] using wordTrace_append hprefix tailTrace_480199
  have hstable : (prefixWord ++ tailWord_480199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480199).length < 2 ^ (prefixWord ++ tailWord_480199).sum := by decide
  have hdescent : baseEnd_480199 < baseStart_480199 := by decide
  rcases family_descends (prefixWord ++ tailWord_480199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480316 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_480316 : Nat := 118140960795 + 480316 * 2 ^ 59
def prefixEnd_480316 : Nat := 4983230072969 + 3 ^ 40 * 480316 * 2
def baseEnd_480316 : Nat := 82210991348349331713691

theorem tailTrace_480316 : CollatzResearch.WordTrace tailWord_480316 prefixEnd_480316 82210991348349331713691 := by
  unfold tailWord_480316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759281863952319143526401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11679042485269758858035201 8759281863952319143526401)
  ·
    refine ⟨6569461397964239357644801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8759281863952319143526401 6569461397964239357644801)
    ·
      refine ⟨4927096048473179518233601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6569461397964239357644801 4927096048473179518233601)
      ·
        refine ⟨3695322036354884638675201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927096048473179518233601 3695322036354884638675201)
        ·
          refine ⟨2771491527266163479006401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695322036354884638675201 2771491527266163479006401)
          ·
            refine ⟨2078618645449622609254801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771491527266163479006401 2078618645449622609254801)
            ·
              refine ⟨1558963984087216956941101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078618645449622609254801 1558963984087216956941101)
              ·
                refine ⟨584611494032706358852913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558963984087216956941101 584611494032706358852913)
                ·
                  refine ⟨438458620524529769139685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584611494032706358852913 438458620524529769139685)
                  ·
                    refine ⟨82210991348349331713691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438458620524529769139685 82210991348349331713691)
                    ·
                      rfl

theorem cell23_480316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_480316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480316 prefixEnd_480316 := by exact prefixLift 480316
  have htrace : WordTrace (prefixWord ++ tailWord_480316) baseStart_480316 baseEnd_480316 := by
    simpa [prefixWord, tailWord_480316, baseEnd_480316] using wordTrace_append hprefix tailTrace_480316
  have hstable : (prefixWord ++ tailWord_480316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480316).length < 2 ^ (prefixWord ++ tailWord_480316).sum := by decide
  have hdescent : baseEnd_480316 < baseStart_480316 := by decide
  rcases family_descends (prefixWord ++ tailWord_480316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480340 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_480340 : Nat := 118140960795 + 480340 * 2 ^ 59
def prefixEnd_480340 : Nat := 4983230072969 + 3 ^ 40 * 480340 * 2
def baseEnd_480340 : Nat := 246645297580755901240963

theorem tailTrace_480340 : CollatzResearch.WordTrace tailWord_480340 prefixEnd_480340 246645297580755901240963 := by
  unfold tailWord_480340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759719539908845192963237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11679626053211793590617649 8759719539908845192963237)
  ·
    refine ⟨1642447413732908473680607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8759719539908845192963237 1642447413732908473680607)
    ·
      refine ⟨2463671120599362710520911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642447413732908473680607 2463671120599362710520911)
      ·
        refine ⟨3695506680899044065781367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463671120599362710520911 3695506680899044065781367)
        ·
          refine ⟨5543260021348566098672051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695506680899044065781367 5543260021348566098672051)
          ·
            refine ⟨8314890032022849148008077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543260021348566098672051 8314890032022849148008077)
            ·
              refine ⟨3118083762008568430503029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8314890032022849148008077 3118083762008568430503029)
              ·
                refine ⟨292320352688303290359659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3118083762008568430503029 292320352688303290359659)
                ·
                  refine ⟨438480529032454935539489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292320352688303290359659 438480529032454935539489)
                  ·
                    refine ⟨328860396774341201654617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438480529032454935539489 328860396774341201654617)
                    ·
                      refine ⟨246645297580755901240963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328860396774341201654617 246645297580755901240963)
                      ·
                        rfl

theorem cell23_480340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_480340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480340 prefixEnd_480340 := by exact prefixLift 480340
  have htrace : WordTrace (prefixWord ++ tailWord_480340) baseStart_480340 baseEnd_480340 := by
    simpa [prefixWord, tailWord_480340, baseEnd_480340] using wordTrace_append hprefix tailTrace_480340
  have hstable : (prefixWord ++ tailWord_480340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480340).length < 2 ^ (prefixWord ++ tailWord_480340).sum := by decide
  have hdescent : baseEnd_480340 < baseStart_480340 := by decide
  rcases family_descends (prefixWord ++ tailWord_480340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480350 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_480350 : Nat := 118140960795 + 480350 * 2 ^ 59
def prefixEnd_480350 : Nat := 4983230072969 + 3 ^ 40 * 480350 * 2
def baseEnd_480350 : Nat := 82216810795766954038639

theorem tailTrace_480350 : CollatzResearch.WordTrace tailWord_480350 prefixEnd_480350 82216810795766954038639 := by
  unfold tailWord_480350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189975476222682761723813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11679869206520974729193669 2189975476222682761723813)
  ·
    refine ⟨410620401791753017823215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2189975476222682761723813 410620401791753017823215)
    ·
      refine ⟨615930602687629526734823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410620401791753017823215 615930602687629526734823)
      ·
        refine ⟨923895904031444290102235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615930602687629526734823 923895904031444290102235)
        ·
          refine ⟨1385843856047166435153353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923895904031444290102235 1385843856047166435153353)
          ·
            refine ⟨1039382892035374826365015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385843856047166435153353 1039382892035374826365015)
            ·
              refine ⟨1559074338053062239547523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039382892035374826365015 1559074338053062239547523)
              ·
                refine ⟨2338611507079593359321285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559074338053062239547523 2338611507079593359321285)
                ·
                  refine ⟨438489657577423754872741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338611507079593359321285 438489657577423754872741)
                  ·
                    refine ⟨82216810795766954038639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438489657577423754872741 82216810795766954038639)
                    ·
                      rfl

theorem cell23_480350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_480350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480350 prefixEnd_480350 := by exact prefixLift 480350
  have htrace : WordTrace (prefixWord ++ tailWord_480350) baseStart_480350 baseEnd_480350 := by
    simpa [prefixWord, tailWord_480350, baseEnd_480350] using wordTrace_append hprefix tailTrace_480350
  have hstable : (prefixWord ++ tailWord_480350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480350).length < 2 ^ (prefixWord ++ tailWord_480350).sum := by decide
  have hdescent : baseEnd_480350 < baseStart_480350 := by decide
  rcases family_descends (prefixWord ++ tailWord_480350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480396 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_480396 : Nat := 118140960795 + 480396 * 2 ^ 59
def prefixEnd_480396 : Nat := 4983230072969 + 3 ^ 40 * 480396 * 2
def baseEnd_480396 : Nat := 246674052497407682140705

theorem tailTrace_480396 : CollatzResearch.WordTrace tailWord_480396 prefixEnd_480396 246674052497407682140705 := by
  unfold tailWord_480396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760740783807405974982521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11680987711743207966643361 8760740783807405974982521)
  ·
    refine ⟨6570555587855554481236891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8760740783807405974982521 6570555587855554481236891)
    ·
      refine ⟨9855833381783331721855337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570555587855554481236891 9855833381783331721855337)
      ·
        refine ⟨7391875036337498791391503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855833381783331721855337 7391875036337498791391503)
        ·
          refine ⟨11087812554506248187087255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391875036337498791391503 11087812554506248187087255)
          ·
            refine ⟨16631718831759372280630883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11087812554506248187087255 16631718831759372280630883)
            ·
              refine ⟨24947578247639058420946325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16631718831759372280630883 24947578247639058420946325)
              ·
                refine ⟨1169417730358080863481859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24947578247639058420946325 1169417730358080863481859)
                ·
                  refine ⟨1754126595537121295222789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169417730358080863481859 1754126595537121295222789)
                  ·
                    refine ⟨328898736663210242854273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754126595537121295222789 328898736663210242854273)
                    ·
                      refine ⟨246674052497407682140705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328898736663210242854273 246674052497407682140705)
                      ·
                        rfl

theorem cell23_480396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_480396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480396 prefixEnd_480396 := by exact prefixLift 480396
  have htrace : WordTrace (prefixWord ++ tailWord_480396) baseStart_480396 baseEnd_480396 := by
    simpa [prefixWord, tailWord_480396, baseEnd_480396] using wordTrace_append hprefix tailTrace_480396
  have hstable : (prefixWord ++ tailWord_480396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480396).length < 2 ^ (prefixWord ++ tailWord_480396).sum := by decide
  have hdescent : baseEnd_480396 < baseStart_480396 := by decide
  rcases family_descends (prefixWord ++ tailWord_480396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480413 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_480413 : Nat := 118140960795 + 480413 * 2 ^ 59
def prefixEnd_480413 : Nat := 4983230072969 + 3 ^ 40 * 480413 * 2
def baseEnd_480413 : Nat := 246682781668534115628127

theorem tailTrace_480413 : CollatzResearch.WordTrace tailWord_480413 prefixEnd_480413 246682781668534115628127 := by
  unfold tailWord_480413
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522101608553223853333893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11681401072368815902222595 17522101608553223853333893)
  ·
    refine ⟨3285394051603729472500105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17522101608553223853333893 3285394051603729472500105)
    ·
      refine ⟨2464045538702797104375079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285394051603729472500105 2464045538702797104375079)
      ·
        refine ⟨3696068308054195656562619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2464045538702797104375079 3696068308054195656562619)
        ·
          refine ⟨5544102462081293484843929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696068308054195656562619 5544102462081293484843929)
          ·
            refine ⟨4158076846560970113632947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544102462081293484843929 4158076846560970113632947)
            ·
              refine ⟨6237115269841455170449421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158076846560970113632947 6237115269841455170449421)
              ·
                refine ⟨2338918226190545688918533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6237115269841455170449421 2338918226190545688918533)
                ·
                  refine ⟨438547167410727316672225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2338918226190545688918533 438547167410727316672225)
                  ·
                    refine ⟨328910375558045487504169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438547167410727316672225 328910375558045487504169)
                    ·
                      refine ⟨246682781668534115628127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 328910375558045487504169 246682781668534115628127)
                      ·
                        rfl

theorem cell23_480413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_480413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480413 prefixEnd_480413 := by exact prefixLift 480413
  have htrace : WordTrace (prefixWord ++ tailWord_480413) baseStart_480413 baseEnd_480413 := by
    simpa [prefixWord, tailWord_480413, baseEnd_480413] using wordTrace_append hprefix tailTrace_480413
  have hstable : (prefixWord ++ tailWord_480413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480413).length < 2 ^ (prefixWord ++ tailWord_480413).sum := by decide
  have hdescent : baseEnd_480413 < baseStart_480413 := by decide
  rcases family_descends (prefixWord ++ tailWord_480413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480466 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_480466 : Nat := 118140960795 + 480466 * 2 ^ 59
def prefixEnd_480466 : Nat := 4983230072969 + 3 ^ 40 * 480466 * 2
def baseEnd_480466 : Nat := 82236665381074136088461

theorem tailTrace_480466 : CollatzResearch.WordTrace tailWord_480466 prefixEnd_480466 82236665381074136088461 := by
  unfold tailWord_480466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381008669340303476253313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11682689784907475936675501 4381008669340303476253313)
  ·
    refine ⟨3285756502005227607189985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4381008669340303476253313 3285756502005227607189985)
    ·
      refine ⟨2464317376503920705392489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285756502005227607189985 2464317376503920705392489)
      ·
        refine ⟨1848238032377940529044367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2464317376503920705392489 1848238032377940529044367)
        ·
          refine ⟨2772357048566910793566551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848238032377940529044367 2772357048566910793566551)
          ·
            refine ⟨4158535572850366190349827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772357048566910793566551 4158535572850366190349827)
            ·
              refine ⟨6237803359275549285524741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158535572850366190349827 6237803359275549285524741)
              ·
                refine ⟨1169588129864165491035889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6237803359275549285524741 1169588129864165491035889)
                ·
                  refine ⟨877191097398124118276917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169588129864165491035889 877191097398124118276917)
                  ·
                    refine ⟨82236665381074136088461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 877191097398124118276917 82236665381074136088461)
                    ·
                      rfl

theorem cell23_480466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_480466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480466 prefixEnd_480466 := by exact prefixLift 480466
  have htrace : WordTrace (prefixWord ++ tailWord_480466) baseStart_480466 baseEnd_480466 := by
    simpa [prefixWord, tailWord_480466, baseEnd_480466] using wordTrace_append hprefix tailTrace_480466
  have hstable : (prefixWord ++ tailWord_480466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480466).length < 2 ^ (prefixWord ++ tailWord_480466).sum := by decide
  have hdescent : baseEnd_480466 < baseStart_480466 := by decide
  rcases family_descends (prefixWord ++ tailWord_480466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480506 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_480506 : Nat := 118140960795 + 480506 * 2 ^ 59
def prefixEnd_480506 : Nat := 4983230072969 + 3 ^ 40 * 480506 * 2
def baseEnd_480506 : Nat := 246730535369402251765199

theorem tailTrace_480506 : CollatzResearch.WordTrace tailWord_480506 prefixEnd_480506 246730535369402251765199 := by
  unfold tailWord_480506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381373399304075184117343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11683662398144200490979581 4381373399304075184117343)
  ·
    refine ⟨6572060098956112776176015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4381373399304075184117343 6572060098956112776176015)
    ·
      refine ⟨9858090148434169164264023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572060098956112776176015 9858090148434169164264023)
      ·
        refine ⟨14787135222651253746396035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858090148434169164264023 14787135222651253746396035)
        ·
          refine ⟨22180702833976880619594053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14787135222651253746396035 22180702833976880619594053)
          ·
            refine ⟨4158881781370665116173885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22180702833976880619594053 4158881781370665116173885)
            ·
              refine ⟨1559580668013999418565207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4158881781370665116173885 1559580668013999418565207)
              ·
                refine ⟨2339371002020999127847811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559580668013999418565207 2339371002020999127847811)
                ·
                  refine ⟨3509056503031498691771717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339371002020999127847811 3509056503031498691771717)
                  ·
                    refine ⟨657948094318406004707197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3509056503031498691771717 657948094318406004707197)
                    ·
                      refine ⟨246730535369402251765199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 657948094318406004707197 246730535369402251765199)
                      ·
                        rfl

theorem cell23_480506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_480506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480506 prefixEnd_480506 := by exact prefixLift 480506
  have htrace : WordTrace (prefixWord ++ tailWord_480506) baseStart_480506 baseEnd_480506 := by
    simpa [prefixWord, tailWord_480506, baseEnd_480506] using wordTrace_append hprefix tailTrace_480506
  have hstable : (prefixWord ++ tailWord_480506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480506).length < 2 ^ (prefixWord ++ tailWord_480506).sum := by decide
  have hdescent : baseEnd_480506 < baseStart_480506 := by decide
  rcases family_descends (prefixWord ++ tailWord_480506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480516 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_480516 : Nat := 118140960795 + 480516 * 2 ^ 59
def prefixEnd_480516 : Nat := 4983230072969 + 3 ^ 40 * 480516 * 2
def baseEnd_480516 : Nat := 246735670175947212640153

theorem tailTrace_480516 : CollatzResearch.WordTrace tailWord_480516 prefixEnd_480516 246735670175947212640153 := by
  unfold tailWord_480516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762929163590036222166701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11683905551453381629555601 8762929163590036222166701)
  ·
    refine ⟨3286098436346263583312513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8762929163590036222166701 3286098436346263583312513)
    ·
      refine ⟨2464573827259697687484385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286098436346263583312513 2464573827259697687484385)
      ·
        refine ⟨1848430370444773265613289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2464573827259697687484385 1848430370444773265613289)
        ·
          refine ⟨1386322777833579949209967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848430370444773265613289 1386322777833579949209967)
          ·
            refine ⟨2079484166750369923814951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386322777833579949209967 2079484166750369923814951)
            ·
              refine ⟨3119226250125554885722427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079484166750369923814951 3119226250125554885722427)
              ·
                refine ⟨4678839375188332328583641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119226250125554885722427 4678839375188332328583641)
                ·
                  refine ⟨3509129531391249246437731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4678839375188332328583641 3509129531391249246437731)
                  ·
                    refine ⟨5263694297086873869656597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3509129531391249246437731 5263694297086873869656597)
                    ·
                      refine ⟨246735670175947212640153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5263694297086873869656597 246735670175947212640153)
                      ·
                        rfl

theorem cell23_480516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_480516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480516 prefixEnd_480516 := by exact prefixLift 480516
  have htrace : WordTrace (prefixWord ++ tailWord_480516) baseStart_480516 baseEnd_480516 := by
    simpa [prefixWord, tailWord_480516, baseEnd_480516] using wordTrace_append hprefix tailTrace_480516
  have hstable : (prefixWord ++ tailWord_480516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480516).length < 2 ^ (prefixWord ++ tailWord_480516).sum := by decide
  have hdescent : baseEnd_480516 < baseStart_480516 := by decide
  rcases family_descends (prefixWord ++ tailWord_480516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480526 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_480526 : Nat := 118140960795 + 480526 * 2 ^ 59
def prefixEnd_480526 : Nat := 4983230072969 + 3 ^ 40 * 480526 * 2
def baseEnd_480526 : Nat := 27415644998054685946123

theorem tailTrace_480526 : CollatzResearch.WordTrace tailWord_480526 prefixEnd_480526 27415644998054685946123 := by
  unfold tailWord_480526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190777882142980519024679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11684148704762562768131621 2190777882142980519024679)
  ·
    refine ⟨3286166823214470778537019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190777882142980519024679 3286166823214470778537019)
    ·
      refine ⟨4929250234821706167805529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286166823214470778537019 4929250234821706167805529)
      ·
        refine ⟨3696937676116279625854147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929250234821706167805529 3696937676116279625854147)
        ·
          refine ⟨5545406514174419438781221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696937676116279625854147 5545406514174419438781221)
          ·
            refine ⟨1039763721407703644771479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5545406514174419438781221 1039763721407703644771479)
            ·
              refine ⟨1559645582111555467157219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039763721407703644771479 1559645582111555467157219)
              ·
                refine ⟨2339468373167333200735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559645582111555467157219 2339468373167333200735829)
                ·
                  refine ⟨27415644998054685946123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2339468373167333200735829 27415644998054685946123)
                  ·
                    rfl

theorem cell23_480526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_480526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480526 prefixEnd_480526 := by exact prefixLift 480526
  have htrace : WordTrace (prefixWord ++ tailWord_480526) baseStart_480526 baseEnd_480526 := by
    simpa [prefixWord, tailWord_480526, baseEnd_480526] using wordTrace_append hprefix tailTrace_480526
  have hstable : (prefixWord ++ tailWord_480526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480526).length < 2 ^ (prefixWord ++ tailWord_480526).sum := by decide
  have hdescent : baseEnd_480526 < baseStart_480526 := by decide
  rcases family_descends (prefixWord ++ tailWord_480526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480529 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_480529 : Nat := 118140960795 + 480529 * 2 ^ 59
def prefixEnd_480529 : Nat := 4983230072969 + 3 ^ 40 * 480529 * 2
def baseEnd_480529 : Nat := 246742345424455661777593

theorem tailTrace_480529 : CollatzResearch.WordTrace tailWord_480529 prefixEnd_480529 246742345424455661777593 := by
  unfold tailWord_480529
  simp only [CollatzResearch.WordTrace]
  refine ⟨17526332476132975664556641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11684221650755317109704427 17526332476132975664556641)
  ·
    refine ⟨13144749357099731748417481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17526332476132975664556641 13144749357099731748417481)
    ·
      refine ⟨9858562017824798811313111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13144749357099731748417481 9858562017824798811313111)
      ·
        refine ⟨14787843026737198216969667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858562017824798811313111 14787843026737198216969667)
        ·
          refine ⟨22181764540105797325454501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14787843026737198216969667 22181764540105797325454501)
          ·
            refine ⟨4159080851269836998522719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22181764540105797325454501 4159080851269836998522719)
            ·
              refine ⟨6238621276904755497784079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159080851269836998522719 6238621276904755497784079)
              ·
                refine ⟨9357931915357133246676119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238621276904755497784079 9357931915357133246676119)
                ·
                  refine ⟨14036897873035699870014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357931915357133246676119 14036897873035699870014179)
                  ·
                    refine ⟨21055346809553549805021269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14036897873035699870014179 21055346809553549805021269)
                    ·
                      refine ⟨246742345424455661777593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21055346809553549805021269 246742345424455661777593)
                      ·
                        rfl

theorem cell23_480529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_480529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480529 prefixEnd_480529 := by exact prefixLift 480529
  have htrace : WordTrace (prefixWord ++ tailWord_480529) baseStart_480529 baseEnd_480529 := by
    simpa [prefixWord, tailWord_480529, baseEnd_480529] using wordTrace_append hprefix tailTrace_480529
  have hstable : (prefixWord ++ tailWord_480529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480529).length < 2 ^ (prefixWord ++ tailWord_480529).sum := by decide
  have hdescent : baseEnd_480529 < baseStart_480529 := by decide
  rcases family_descends (prefixWord ++ tailWord_480529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480563 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 5, 2]
def baseStart_480563 : Nat := 118140960795 + 480563 * 2 ^ 59
def prefixEnd_480563 : Nat := 4983230072969 + 3 ^ 40 * 480563 * 2
def baseEnd_480563 : Nat := 246759803766708528752437

theorem tailTrace_480563 : CollatzResearch.WordTrace tailWord_480563 prefixEnd_480563 246759803766708528752437 := by
  unfold tailWord_480563
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527572558009799471294343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11685048372006532980862895 17527572558009799471294343)
  ·
    refine ⟨26291358837014699206941515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17527572558009799471294343 26291358837014699206941515)
    ·
      refine ⟨39437038255522048810412273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26291358837014699206941515 39437038255522048810412273)
      ·
        refine ⟨29577778691641536607809205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39437038255522048810412273 29577778691641536607809205)
        ·
          refine ⟨2772916752341394056982113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29577778691641536607809205 2772916752341394056982113)
          ·
            refine ⟨2079687564256045542736585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772916752341394056982113 2079687564256045542736585)
            ·
              refine ⟨1559765673192034157052439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079687564256045542736585 1559765673192034157052439)
              ·
                refine ⟨2339648509788051235578659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559765673192034157052439 2339648509788051235578659)
                ·
                  refine ⟨3509472764682076853367989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339648509788051235578659 3509472764682076853367989)
                  ·
                    refine ⟨329013071688944705003249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3509472764682076853367989 329013071688944705003249)
                    ·
                      refine ⟨246759803766708528752437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329013071688944705003249 246759803766708528752437)
                      ·
                        rfl

theorem cell23_480563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 5, 2].length) (baseStart_480563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480563 prefixEnd_480563 := by exact prefixLift 480563
  have htrace : WordTrace (prefixWord ++ tailWord_480563) baseStart_480563 baseEnd_480563 := by
    simpa [prefixWord, tailWord_480563, baseEnd_480563] using wordTrace_append hprefix tailTrace_480563
  have hstable : (prefixWord ++ tailWord_480563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480563).length < 2 ^ (prefixWord ++ tailWord_480563).sum := by decide
  have hdescent : baseEnd_480563 < baseStart_480563 := by decide
  rcases family_descends (prefixWord ++ tailWord_480563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480613 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_480613 : Nat := 118140960795 + 480613 * 2 ^ 59
def prefixEnd_480613 : Nat := 4983230072969 + 3 ^ 40 * 480613 * 2
def baseEnd_480613 : Nat := 246785477799433333127207

theorem tailTrace_480613 : CollatzResearch.WordTrace tailWord_480613 prefixEnd_480613 246785477799433333127207 := by
  unfold tailWord_480613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529396207828658010614493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11686264138552438673742995 17529396207828658010614493)
  ·
    refine ⟨6573523577935746753980435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17529396207828658010614493 6573523577935746753980435)
    ·
      refine ⟨9860285366903620130970653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6573523577935746753980435 9860285366903620130970653)
      ·
        refine ⟨3697607012588857549113995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9860285366903620130970653 3697607012588857549113995)
        ·
          refine ⟨5546410518883286323670993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697607012588857549113995 5546410518883286323670993)
          ·
            refine ⟨4159807889162464742753245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546410518883286323670993 4159807889162464742753245)
            ·
              refine ⟨1559927958435924278532467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4159807889162464742753245 1559927958435924278532467)
              ·
                refine ⟨2339891937653886417798701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559927958435924278532467 2339891937653886417798701)
                ·
                  refine ⟨877459476620207406674513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2339891937653886417798701 877459476620207406674513)
                  ·
                    refine ⟨658094607465155555005885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 877459476620207406674513 658094607465155555005885)
                    ·
                      refine ⟨246785477799433333127207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 658094607465155555005885 246785477799433333127207)
                      ·
                        rfl

theorem cell23_480613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_480613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480613 prefixEnd_480613 := by exact prefixLift 480613
  have htrace : WordTrace (prefixWord ++ tailWord_480613) baseStart_480613 baseEnd_480613 := by
    simpa [prefixWord, tailWord_480613, baseEnd_480613] using wordTrace_append hprefix tailTrace_480613
  have hstable : (prefixWord ++ tailWord_480613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480613).length < 2 ^ (prefixWord ++ tailWord_480613).sum := by decide
  have hdescent : baseEnd_480613 < baseStart_480613 := by decide
  rcases family_descends (prefixWord ++ tailWord_480613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480644 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_480644 : Nat := 118140960795 + 480644 * 2 ^ 59
def prefixEnd_480644 : Nat := 4983230072969 + 3 ^ 40 * 480644 * 2
def baseEnd_480644 : Nat := 246801395699722711839565

theorem tailTrace_480644 : CollatzResearch.WordTrace tailWord_480644 prefixEnd_480644 246801395699722711839565 := by
  unfold tailWord_480644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765263435358175152496493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687017913810900203328657 8765263435358175152496493)
  ·
    refine ⟨3286973788259315682186185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8765263435358175152496493 3286973788259315682186185)
    ·
      refine ⟨2465230341194486761639639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286973788259315682186185 2465230341194486761639639)
      ·
        refine ⟨3697845511791730142459459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465230341194486761639639 3697845511791730142459459)
        ·
          refine ⟨5546768267687595213689189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697845511791730142459459 5546768267687595213689189)
          ·
            refine ⟨1040019050191424102566723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5546768267687595213689189 1040019050191424102566723)
            ·
              refine ⟨1560028575287136153850085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040019050191424102566723 1560028575287136153850085)
              ·
                refine ⟨292505357866338028846891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1560028575287136153850085 292505357866338028846891)
                ·
                  refine ⟨438758036799507043270337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292505357866338028846891 438758036799507043270337)
                  ·
                    refine ⟨329068527599630282452753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438758036799507043270337 329068527599630282452753)
                    ·
                      refine ⟨246801395699722711839565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329068527599630282452753 246801395699722711839565)
                      ·
                        rfl

theorem cell23_480644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_480644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480644 prefixEnd_480644 := by exact prefixLift 480644
  have htrace : WordTrace (prefixWord ++ tailWord_480644) baseStart_480644 baseEnd_480644 := by
    simpa [prefixWord, tailWord_480644, baseEnd_480644] using wordTrace_append hprefix tailTrace_480644
  have hstable : (prefixWord ++ tailWord_480644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480644).length < 2 ^ (prefixWord ++ tailWord_480644).sum := by decide
  have hdescent : baseEnd_480644 < baseStart_480644 := by decide
  rcases family_descends (prefixWord ++ tailWord_480644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480660 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_480660 : Nat := 118140960795 + 480660 * 2 ^ 59
def prefixEnd_480660 : Nat := 4983230072969 + 3 ^ 40 * 480660 * 2
def baseEnd_480660 : Nat := 246809611390194649239491

theorem tailTrace_480660 : CollatzResearch.WordTrace tailWord_480660 prefixEnd_480660 246809611390194649239491 := by
  unfold tailWord_480660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765555219329192518787717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687406959105590025050289 8765555219329192518787717)
  ·
    refine ⟨1643541603624223597272697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8765555219329192518787717 1643541603624223597272697)
    ·
      refine ⟨1232656202718167697954523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1643541603624223597272697 1232656202718167697954523)
      ·
        refine ⟨1848984304077251546931785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232656202718167697954523 1848984304077251546931785)
        ·
          refine ⟨1386738228057938660198839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848984304077251546931785 1386738228057938660198839)
          ·
            refine ⟨2080107342086907990298259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386738228057938660198839 2080107342086907990298259)
            ·
              refine ⟨3120161013130361985447389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080107342086907990298259 3120161013130361985447389)
              ·
                refine ⟨1170060379923885744542771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3120161013130361985447389 1170060379923885744542771)
                ·
                  refine ⟨1755090569885828616814157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170060379923885744542771 1755090569885828616814157)
                  ·
                    refine ⟨658158963707185731305309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1755090569885828616814157 658158963707185731305309)
                    ·
                      refine ⟨246809611390194649239491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 658158963707185731305309 246809611390194649239491)
                      ·
                        rfl

theorem cell23_480660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_480660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480660 prefixEnd_480660 := by exact prefixLift 480660
  have htrace : WordTrace (prefixWord ++ tailWord_480660) baseStart_480660 baseEnd_480660 := by
    simpa [prefixWord, tailWord_480660, baseEnd_480660] using wordTrace_append hprefix tailTrace_480660
  have hstable : (prefixWord ++ tailWord_480660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480660).length < 2 ^ (prefixWord ++ tailWord_480660).sum := by decide
  have hdescent : baseEnd_480660 < baseStart_480660 := by decide
  rcases family_descends (prefixWord ++ tailWord_480660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480676 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_480676 : Nat := 118140960795 + 480676 * 2 ^ 59
def prefixEnd_480676 : Nat := 4983230072969 + 3 ^ 40 * 480676 * 2
def baseEnd_480676 : Nat := 82272609026888862213139

theorem tailTrace_480676 : CollatzResearch.WordTrace tailWord_480676 prefixEnd_480676 82272609026888862213139 := by
  unfold tailWord_480676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765847003300209885078941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11687796004400279846771921 8765847003300209885078941)
  ·
    refine ⟨3287192626237578706904603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8765847003300209885078941 3287192626237578706904603)
    ·
      refine ⟨4930788939356368060356905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287192626237578706904603 4930788939356368060356905)
      ·
        refine ⟨3698091704517276045267679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4930788939356368060356905 3698091704517276045267679)
        ·
          refine ⟨5547137556775914067901519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3698091704517276045267679 5547137556775914067901519)
          ·
            refine ⟨8320706335163871101852279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547137556775914067901519 8320706335163871101852279)
            ·
              refine ⟨12481059502745806652778419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320706335163871101852279 12481059502745806652778419)
              ·
                refine ⟨18721589254118709979167629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12481059502745806652778419 18721589254118709979167629)
                ·
                  refine ⟨7020595970294516242187861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18721589254118709979167629 7020595970294516242187861)
                  ·
                    refine ⟨82272609026888862213139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7020595970294516242187861 82272609026888862213139)
                    ·
                      rfl

theorem cell23_480676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_480676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480676 prefixEnd_480676 := by exact prefixLift 480676
  have htrace : WordTrace (prefixWord ++ tailWord_480676) baseStart_480676 baseEnd_480676 := by
    simpa [prefixWord, tailWord_480676, baseEnd_480676] using wordTrace_append hprefix tailTrace_480676
  have hstable : (prefixWord ++ tailWord_480676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480676).length < 2 ^ (prefixWord ++ tailWord_480676).sum := by decide
  have hdescent : baseEnd_480676 < baseStart_480676 := by decide
  rcases family_descends (prefixWord ++ tailWord_480676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480683 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 4, 2]
def baseStart_480683 : Nat := 118140960795 + 480683 * 2 ^ 59
def prefixEnd_480683 : Nat := 4983230072969 + 3 ^ 40 * 480683 * 2
def baseEnd_480683 : Nat := 246821421445248059251885

theorem tailTrace_480683 : CollatzResearch.WordTrace tailWord_480683 prefixEnd_480683 246821421445248059251885 := by
  unfold tailWord_480683
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531949317575059965662703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11687966211716706643775135 17531949317575059965662703)
  ·
    refine ⟨26297923976362589948494055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17531949317575059965662703 26297923976362589948494055)
    ·
      refine ⟨39446885964543884922741083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26297923976362589948494055 39446885964543884922741083)
      ·
        refine ⟨59170328946815827384111625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39446885964543884922741083 59170328946815827384111625)
        ·
          refine ⟨44377746710111870538083719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59170328946815827384111625 44377746710111870538083719)
          ·
            refine ⟨66566620065167805807125579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44377746710111870538083719 66566620065167805807125579)
            ·
              refine ⟨99849930097751708710688369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66566620065167805807125579 99849930097751708710688369)
              ·
                refine ⟨74887447573313781533016277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99849930097751708710688369 74887447573313781533016277)
                ·
                  refine ⟨1755174552499541754680069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74887447573313781533016277 1755174552499541754680069)
                  ·
                    refine ⟨329095228593664079002513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755174552499541754680069 329095228593664079002513)
                    ·
                      refine ⟨246821421445248059251885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329095228593664079002513 246821421445248059251885)
                      ·
                        rfl

theorem cell23_480683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 4, 2].length) (baseStart_480683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480683 prefixEnd_480683 := by exact prefixLift 480683
  have htrace : WordTrace (prefixWord ++ tailWord_480683) baseStart_480683 baseEnd_480683 := by
    simpa [prefixWord, tailWord_480683, baseEnd_480683] using wordTrace_append hprefix tailTrace_480683
  have hstable : (prefixWord ++ tailWord_480683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480683).length < 2 ^ (prefixWord ++ tailWord_480683).sum := by decide
  have hdescent : baseEnd_480683 < baseStart_480683 := by decide
  rcases family_descends (prefixWord ++ tailWord_480683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480693 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_480693 : Nat := 118140960795 + 480693 * 2 ^ 59
def prefixEnd_480693 : Nat := 4983230072969 + 3 ^ 40 * 480693 * 2
def baseEnd_480693 : Nat := 82275518750597673375613

theorem tailTrace_480693 : CollatzResearch.WordTrace tailWord_480693 prefixEnd_480693 82275518750597673375613 := by
  unfold tailWord_480693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532314047538831673526733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11688209365025887782351155 17532314047538831673526733)
  ·
    refine ⟨6574617767827061877572525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17532314047538831673526733 6574617767827061877572525)
    ·
      refine ⟨2465481662935148204089697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6574617767827061877572525 2465481662935148204089697)
      ·
        refine ⟨1849111247201361153067273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2465481662935148204089697 1849111247201361153067273)
        ·
          refine ⟨1386833435401020864800455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849111247201361153067273 1386833435401020864800455)
          ·
            refine ⟨2080250153101531297200683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386833435401020864800455 2080250153101531297200683)
            ·
              refine ⟨3120375229652296945801025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080250153101531297200683 3120375229652296945801025)
              ·
                refine ⟨2340281422239222709350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120375229652296945801025 2340281422239222709350769)
                ·
                  refine ⟨1755211066679417032013077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340281422239222709350769 1755211066679417032013077)
                  ·
                    refine ⟨82275518750597673375613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1755211066679417032013077 82275518750597673375613)
                    ·
                      rfl

theorem cell23_480693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_480693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480693 prefixEnd_480693 := by exact prefixLift 480693
  have htrace : WordTrace (prefixWord ++ tailWord_480693) baseStart_480693 baseEnd_480693 := by
    simpa [prefixWord, tailWord_480693, baseEnd_480693] using wordTrace_append hprefix tailTrace_480693
  have hstable : (prefixWord ++ tailWord_480693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480693).length < 2 ^ (prefixWord ++ tailWord_480693).sum := by decide
  have hdescent : baseEnd_480693 < baseStart_480693 := by decide
  rcases family_descends (prefixWord ++ tailWord_480693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480753 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_480753 : Nat := 118140960795 + 480753 * 2 ^ 59
def prefixEnd_480753 : Nat := 4983230072969 + 3 ^ 40 * 480753 * 2
def baseEnd_480753 : Nat := 82285788363687595125521

theorem tailTrace_480753 : CollatzResearch.WordTrace tailWord_480753 prefixEnd_480753 82285788363687595125521 := by
  unfold tailWord_480753
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534502427321461920710913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11689668284880974613807275 17534502427321461920710913)
  ·
    refine ⟨13150876820491096440533185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17534502427321461920710913 13150876820491096440533185)
    ·
      refine ⟨9863157615368322330399889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13150876820491096440533185 9863157615368322330399889)
      ·
        refine ⟨7397368211526241747799917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9863157615368322330399889 7397368211526241747799917)
        ·
          refine ⟨2774013079322340655424969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7397368211526241747799917 2774013079322340655424969)
          ·
            refine ⟨2080509809491755491568727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774013079322340655424969 2080509809491755491568727)
            ·
              refine ⟨3120764714237633237353091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080509809491755491568727 3120764714237633237353091)
              ·
                refine ⟨4681147071356449856029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120764714237633237353091 4681147071356449856029637)
                ·
                  refine ⟨877715075879334348005557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4681147071356449856029637 877715075879334348005557)
                  ·
                    refine ⟨82285788363687595125521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 877715075879334348005557 82285788363687595125521)
                    ·
                      rfl

theorem cell23_480753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_480753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480753 prefixEnd_480753 := by exact prefixLift 480753
  have htrace : WordTrace (prefixWord ++ tailWord_480753) baseStart_480753 baseEnd_480753 := by
    simpa [prefixWord, tailWord_480753, baseEnd_480753] using wordTrace_append hprefix tailTrace_480753
  have hstable : (prefixWord ++ tailWord_480753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480753).length < 2 ^ (prefixWord ++ tailWord_480753).sum := by decide
  have hdescent : baseEnd_480753 < baseStart_480753 := by decide
  rcases family_descends (prefixWord ++ tailWord_480753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480757 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 7]
def baseStart_480757 : Nat := 118140960795 + 480757 * 2 ^ 59
def prefixEnd_480757 : Nat := 4983230072969 + 3 ^ 40 * 480757 * 2
def baseEnd_480757 : Nat := 27428824334853418858505

theorem tailTrace_480757 : CollatzResearch.WordTrace tailWord_480757 prefixEnd_480757 27428824334853418858505 := by
  unfold tailWord_480757
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534648319306970603856525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11689765546204647069237683 17534648319306970603856525)
  ·
    refine ⟨6575493119740113976446197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17534648319306970603856525 6575493119740113976446197)
    ·
      refine ⟨616452479975635685291831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6575493119740113976446197 616452479975635685291831)
      ·
        refine ⟨924678719963453527937747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616452479975635685291831 924678719963453527937747)
        ·
          refine ⟨1387018079945180291906621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924678719963453527937747 1387018079945180291906621)
          ·
            refine ⟨520131779979442609464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1387018079945180291906621 520131779979442609464983)
            ·
              refine ⟨780197669969163914197475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520131779979442609464983 780197669969163914197475)
              ·
                refine ⟨1170296504953745871296213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780197669969163914197475 1170296504953745871296213)
                ·
                  refine ⟨27428824334853418858505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1170296504953745871296213 27428824334853418858505)
                  ·
                    rfl

theorem cell23_480757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_480757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480757 prefixEnd_480757 := by exact prefixLift 480757
  have htrace : WordTrace (prefixWord ++ tailWord_480757) baseStart_480757 baseEnd_480757 := by
    simpa [prefixWord, tailWord_480757, baseEnd_480757] using wordTrace_append hprefix tailTrace_480757
  have hstable : (prefixWord ++ tailWord_480757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480757).length < 2 ^ (prefixWord ++ tailWord_480757).sum := by decide
  have hdescent : baseEnd_480757 < baseStart_480757 := by decide
  rcases family_descends (prefixWord ++ tailWord_480757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480773 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_480773 : Nat := 118140960795 + 480773 * 2 ^ 59
def prefixEnd_480773 : Nat := 4983230072969 + 3 ^ 40 * 480773 * 2
def baseEnd_480773 : Nat := 246867634704152707126471

theorem tailTrace_480773 : CollatzResearch.WordTrace tailWord_480773 prefixEnd_480773 246867634704152707126471 := by
  unfold tailWord_480773
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535231887249005336438973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11690154591499336890959315 17535231887249005336438973)
  ·
    refine ⟨6575711957718377001164615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17535231887249005336438973 6575711957718377001164615)
    ·
      refine ⟨9863567936577565501746923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575711957718377001164615 9863567936577565501746923)
      ·
        refine ⟨14795351904866348252620385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9863567936577565501746923 14795351904866348252620385)
        ·
          refine ⟨11096513928649761189465289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14795351904866348252620385 11096513928649761189465289)
          ·
            refine ⟨8322385446487320892098967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096513928649761189465289 8322385446487320892098967)
            ·
              refine ⟨12483578169730981338148451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322385446487320892098967 12483578169730981338148451)
              ·
                refine ⟨18725367254596472007222677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483578169730981338148451 18725367254596472007222677)
                ·
                  refine ⟨877751590059209625338563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18725367254596472007222677 877751590059209625338563)
                  ·
                    refine ⟨1316627385088814438007845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877751590059209625338563 1316627385088814438007845)
                    ·
                      refine ⟨246867634704152707126471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1316627385088814438007845 246867634704152707126471)
                      ·
                        rfl

theorem cell23_480773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_480773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480773 prefixEnd_480773 := by exact prefixLift 480773
  have htrace : WordTrace (prefixWord ++ tailWord_480773) baseStart_480773 baseEnd_480773 := by
    simpa [prefixWord, tailWord_480773, baseEnd_480773] using wordTrace_append hprefix tailTrace_480773
  have hstable : (prefixWord ++ tailWord_480773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480773).length < 2 ^ (prefixWord ++ tailWord_480773).sum := by decide
  have hdescent : baseEnd_480773 < baseStart_480773 := by decide
  rcases family_descends (prefixWord ++ tailWord_480773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480853 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_480853 : Nat := 118140960795 + 480853 * 2 ^ 59
def prefixEnd_480853 : Nat := 4983230072969 + 3 ^ 40 * 480853 * 2
def baseEnd_480853 : Nat := 246908713156512394126103

theorem tailTrace_480853 : CollatzResearch.WordTrace tailWord_480853 prefixEnd_480853 246908713156512394126103 := by
  unfold tailWord_480853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538149726959178999351213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11692099817972785999567475 17538149726959178999351213)
  ·
    refine ⟨6576806147609692124756705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17538149726959178999351213 6576806147609692124756705)
    ·
      refine ⟨4932604610707269093567529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6576806147609692124756705 4932604610707269093567529)
      ·
        refine ⟨3699453458030451820175647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4932604610707269093567529 3699453458030451820175647)
        ·
          refine ⟨5549180187045677730263471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699453458030451820175647 5549180187045677730263471)
          ·
            refine ⟨8323770280568516595395207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549180187045677730263471 8323770280568516595395207)
            ·
              refine ⟨12485655420852774893092811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323770280568516595395207 12485655420852774893092811)
              ·
                refine ⟨18728483131279162339639217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485655420852774893092811 18728483131279162339639217)
                ·
                  refine ⟨14046362348459371754729413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18728483131279162339639217 14046362348459371754729413)
                  ·
                    refine ⟨2633692940336132204011765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14046362348459371754729413 2633692940336132204011765)
                    ·
                      refine ⟨246908713156512394126103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2633692940336132204011765 246908713156512394126103)
                      ·
                        rfl

theorem cell23_480853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_480853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480853 prefixEnd_480853 := by exact prefixLift 480853
  have htrace : WordTrace (prefixWord ++ tailWord_480853) baseStart_480853 baseEnd_480853 := by
    simpa [prefixWord, tailWord_480853, baseEnd_480853] using wordTrace_append hprefix tailTrace_480853
  have hstable : (prefixWord ++ tailWord_480853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480853).length < 2 ^ (prefixWord ++ tailWord_480853).sum := by decide
  have hdescent : baseEnd_480853 < baseStart_480853 := by decide
  rcases family_descends (prefixWord ++ tailWord_480853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480873 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_480873 : Nat := 118140960795 + 480873 * 2 ^ 59
def prefixEnd_480873 : Nat := 4983230072969 + 3 ^ 40 * 480873 * 2
def baseEnd_480873 : Nat := 82306327589867438625337

theorem tailTrace_480873 : CollatzResearch.WordTrace tailWord_480873 prefixEnd_480873 82306327589867438625337 := by
  unfold tailWord_480873
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538879186886722415079273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11692586124591148276719515 17538879186886722415079273)
  ·
    refine ⟨13154159390165041811309455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17538879186886722415079273 13154159390165041811309455)
    ·
      refine ⟨19731239085247562716964183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154159390165041811309455 19731239085247562716964183)
      ·
        refine ⟨29596858627871344075446275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731239085247562716964183 29596858627871344075446275)
        ·
          refine ⟨44395287941807016113169413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29596858627871344075446275 44395287941807016113169413)
          ·
            refine ⟨8324116489088815521219265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44395287941807016113169413 8324116489088815521219265)
            ·
              refine ⟨6243087366816611640914449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8324116489088815521219265 6243087366816611640914449)
              ·
                refine ⟨4682315525112458730685837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243087366816611640914449 4682315525112458730685837)
                ·
                  refine ⟨1755868321917172024007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4682315525112458730685837 1755868321917172024007189)
                  ·
                    refine ⟨82306327589867438625337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1755868321917172024007189 82306327589867438625337)
                    ·
                      rfl

theorem cell23_480873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_480873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480873 prefixEnd_480873 := by exact prefixLift 480873
  have htrace : WordTrace (prefixWord ++ tailWord_480873) baseStart_480873 baseEnd_480873 := by
    simpa [prefixWord, tailWord_480873, baseEnd_480873] using wordTrace_append hprefix tailTrace_480873
  have hstable : (prefixWord ++ tailWord_480873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480873).length < 2 ^ (prefixWord ++ tailWord_480873).sum := by decide
  have hdescent : baseEnd_480873 < baseStart_480873 := by decide
  rcases family_descends (prefixWord ++ tailWord_480873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480874 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_480874 : Nat := 118140960795 + 480874 * 2 ^ 59
def prefixEnd_480874 : Nat := 4983230072969 + 3 ^ 40 * 480874 * 2
def baseEnd_480874 : Nat := 246919496250256811963507

theorem tailTrace_480874 : CollatzResearch.WordTrace tailWord_480874 prefixEnd_480874 246919496250256811963507 := by
  unfold tailWord_480874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384728914970774896466419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11692610439922066390577117 4384728914970774896466419)
  ·
    refine ⟨6577093372456162344699629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4384728914970774896466419 6577093372456162344699629)
    ·
      refine ⟨2466410014671060879262361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6577093372456162344699629 2466410014671060879262361)
      ·
        refine ⟨1849807511003295659446771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466410014671060879262361 1849807511003295659446771)
        ·
          refine ⟨2774711266504943489170157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849807511003295659446771 2774711266504943489170157)
          ·
            refine ⟨1040516724939353808438809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2774711266504943489170157 1040516724939353808438809)
            ·
              refine ⟨780387543704515356329107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040516724939353808438809 780387543704515356329107)
              ·
                refine ⟨1170581315556773034493661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780387543704515356329107 1170581315556773034493661)
                ·
                  refine ⟨438967993333789887935123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1170581315556773034493661 438967993333789887935123)
                  ·
                    refine ⟨658451990000684831902685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 438967993333789887935123 658451990000684831902685)
                    ·
                      refine ⟨246919496250256811963507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 658451990000684831902685 246919496250256811963507)
                      ·
                        rfl

theorem cell23_480874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_480874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480874 prefixEnd_480874 := by exact prefixLift 480874
  have htrace : WordTrace (prefixWord ++ tailWord_480874) baseStart_480874 baseEnd_480874 := by
    simpa [prefixWord, tailWord_480874, baseEnd_480874] using wordTrace_append hprefix tailTrace_480874
  have hstable : (prefixWord ++ tailWord_480874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480874).length < 2 ^ (prefixWord ++ tailWord_480874).sum := by decide
  have hdescent : baseEnd_480874 < baseStart_480874 := by decide
  rcases family_descends (prefixWord ++ tailWord_480874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480897 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_480897 : Nat := 118140960795 + 480897 * 2 ^ 59
def prefixEnd_480897 : Nat := 4983230072969 + 3 ^ 40 * 480897 * 2
def baseEnd_480897 : Nat := 246931306305310221975901

theorem tailTrace_480897 : CollatzResearch.WordTrace tailWord_480897 prefixEnd_480897 246931306305310221975901 := by
  unfold tailWord_480897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17539754538799774513952945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11693169692533183009301963 17539754538799774513952945)
  ·
    refine ⟨13154815904099830885464709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17539754538799774513952945 13154815904099830885464709)
    ·
      refine ⟨2466527982018718291024633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13154815904099830885464709 2466527982018718291024633)
      ·
        refine ⟨1849895986514038718268475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466527982018718291024633 1849895986514038718268475)
        ·
          refine ⟨2774843979771058077402713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849895986514038718268475 2774843979771058077402713)
          ·
            refine ⟨2081132984828293558052035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2774843979771058077402713 2081132984828293558052035)
            ·
              refine ⟨3121699477242440337078053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081132984828293558052035 3121699477242440337078053)
              ·
                refine ⟨585318651982957563202135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3121699477242440337078053 585318651982957563202135)
                ·
                  refine ⟨877977977974436344803203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585318651982957563202135 877977977974436344803203)
                  ·
                    refine ⟨1316966966961654517204805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 877977977974436344803203 1316966966961654517204805)
                    ·
                      refine ⟨246931306305310221975901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1316966966961654517204805 246931306305310221975901)
                      ·
                        rfl

theorem cell23_480897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_480897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480897 prefixEnd_480897 := by exact prefixLift 480897
  have htrace : WordTrace (prefixWord ++ tailWord_480897) baseStart_480897 baseEnd_480897 := by
    simpa [prefixWord, tailWord_480897, baseEnd_480897] using wordTrace_append hprefix tailTrace_480897
  have hstable : (prefixWord ++ tailWord_480897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480897).length < 2 ^ (prefixWord ++ tailWord_480897).sum := by decide
  have hdescent : baseEnd_480897 < baseStart_480897 := by decide
  rcases family_descends (prefixWord ++ tailWord_480897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480920 : List Nat := [2, 1, 2, 4, 1, 4, 9]
def baseStart_480920 : Nat := 118140960795 + 480920 * 2 ^ 59
def prefixEnd_480920 : Nat := 4983230072969 + 3 ^ 40 * 480920 * 2
def baseEnd_480920 : Nat := 3048680448893378172695

theorem tailTrace_480920 : CollatzResearch.WordTrace tailWord_480920 prefixEnd_480920 3048680448893378172695 := by
  unfold tailWord_480920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770296708858224721020107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11693728945144299628026809 8770296708858224721020107)
  ·
    refine ⟨13155445063287337081530161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770296708858224721020107 13155445063287337081530161)
    ·
      refine ⟨9866583797465502811147621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13155445063287337081530161 9866583797465502811147621)
      ·
        refine ⟨1849984462024781777090179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9866583797465502811147621 1849984462024781777090179)
        ·
          refine ⟨2774976693037172665635269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849984462024781777090179 2774976693037172665635269)
          ·
            refine ⟨520308129944469874806613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2774976693037172665635269 520308129944469874806613)
            ·
              refine ⟨3048680448893378172695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 520308129944469874806613 3048680448893378172695)
              ·
                rfl

theorem cell23_480920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 9].length) (baseStart_480920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480920 prefixEnd_480920 := by exact prefixLift 480920
  have htrace : WordTrace (prefixWord ++ tailWord_480920) baseStart_480920 baseEnd_480920 := by
    simpa [prefixWord, tailWord_480920, baseEnd_480920] using wordTrace_append hprefix tailTrace_480920
  have hstable : (prefixWord ++ tailWord_480920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480920).length < 2 ^ (prefixWord ++ tailWord_480920).sum := by decide
  have hdescent : baseEnd_480920 < baseStart_480920 := by decide
  rcases family_descends (prefixWord ++ tailWord_480920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_480982 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_480982 : Nat := 118140960795 + 480982 * 2 ^ 59
def prefixEnd_480982 : Nat := 4983230072969 + 3 ^ 40 * 480982 * 2
def baseEnd_480982 : Nat := 246974952160942389413011

theorem tailTrace_480982 : CollatzResearch.WordTrace tailWord_480982 prefixEnd_480982 246974952160942389413011 := by
  unfold tailWord_480982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096428421468239626924825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11695236495661222687198133 1096428421468239626924825)
  ·
    refine ⟨822321316101179720193619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1096428421468239626924825 822321316101179720193619)
    ·
      refine ⟨1233481974151769580290429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822321316101179720193619 1233481974151769580290429)
      ·
        refine ⟨462555740306913592608911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1233481974151769580290429 462555740306913592608911)
        ·
          refine ⟨693833610460370388913367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462555740306913592608911 693833610460370388913367)
          ·
            refine ⟨1040750415690555583370051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693833610460370388913367 1040750415690555583370051)
            ·
              refine ⟨1561125623535833375055077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040750415690555583370051 1561125623535833375055077)
              ·
                refine ⟨292711054412968757822827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1561125623535833375055077 292711054412968757822827)
                ·
                  refine ⟨439066581619453136734241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292711054412968757822827 439066581619453136734241)
                  ·
                    refine ⟨329299936214589852550681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439066581619453136734241 329299936214589852550681)
                    ·
                      refine ⟨246974952160942389413011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329299936214589852550681 246974952160942389413011)
                      ·
                        rfl

theorem cell23_480982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_480982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_480982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_480982 prefixEnd_480982 := by exact prefixLift 480982
  have htrace : WordTrace (prefixWord ++ tailWord_480982) baseStart_480982 baseEnd_480982 := by
    simpa [prefixWord, tailWord_480982, baseEnd_480982] using wordTrace_append hprefix tailTrace_480982
  have hstable : (prefixWord ++ tailWord_480982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_480982).length < 2 ^ (prefixWord ++ tailWord_480982).sum := by decide
  have hdescent : baseEnd_480982 < baseStart_480982 := by decide
  rcases family_descends (prefixWord ++ tailWord_480982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481027 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 5]
def baseStart_481027 : Nat := 118140960795 + 481027 * 2 ^ 59
def prefixEnd_481027 : Nat := 4983230072969 + 3 ^ 40 * 481027 * 2
def baseEnd_481027 : Nat := 27444228754488301483367

theorem tailTrace_481027 : CollatzResearch.WordTrace tailWord_481027 prefixEnd_481027 27444228754488301483367 := by
  unfold tailWord_481027
  simp only [CollatzResearch.WordTrace]
  refine ⟨17544496028328806716185335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11696330685552537810790223 17544496028328806716185335)
  ·
    refine ⟨26316744042493210074278003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17544496028328806716185335 26316744042493210074278003)
    ·
      refine ⟨39475116063739815111417005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26316744042493210074278003 39475116063739815111417005)
      ·
        refine ⟨14803168523902430666781377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39475116063739815111417005 14803168523902430666781377)
        ·
          refine ⟨11102376392926823000086033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14803168523902430666781377 11102376392926823000086033)
          ·
            refine ⟨8326782294695117250064525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11102376392926823000086033 8326782294695117250064525)
            ·
              refine ⟨3122543360510668968774197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8326782294695117250064525 3122543360510668968774197)
              ·
                refine ⟨292738440047875215822581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3122543360510668968774197 292738440047875215822581)
                ·
                  refine ⟨27444228754488301483367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292738440047875215822581 27444228754488301483367)
                  ·
                    rfl

theorem cell23_481027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 5].length) (baseStart_481027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481027 prefixEnd_481027 := by exact prefixLift 481027
  have htrace : WordTrace (prefixWord ++ tailWord_481027) baseStart_481027 baseEnd_481027 := by
    simpa [prefixWord, tailWord_481027, baseEnd_481027] using wordTrace_append hprefix tailTrace_481027
  have hstable : (prefixWord ++ tailWord_481027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481027).length < 2 ^ (prefixWord ++ tailWord_481027).sum := by decide
  have hdescent : baseEnd_481027 < baseStart_481027 := by decide
  rcases family_descends (prefixWord ++ tailWord_481027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481078 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_481078 : Nat := 118140960795 + 481078 * 2 ^ 59
def prefixEnd_481078 : Nat := 4983230072969 + 3 ^ 40 * 481078 * 2
def baseEnd_481078 : Nat := 27447138478197112645841

theorem tailTrace_481078 : CollatzResearch.WordTrace tailWord_481078 prefixEnd_481078 27447138478197112645841 := by
  unfold tailWord_481078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096647259446502651643243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11697570767429361617527925 1096647259446502651643243)
  ·
    refine ⟨1644970889169753977464865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096647259446502651643243 1644970889169753977464865)
    ·
      refine ⟨1233728166877315483098649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644970889169753977464865 1233728166877315483098649)
      ·
        refine ⟨925296125157986612323987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233728166877315483098649 925296125157986612323987)
        ·
          refine ⟨1387944187736979918485981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925296125157986612323987 1387944187736979918485981)
          ·
            refine ⟨520479070401367469432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1387944187736979918485981 520479070401367469432243)
            ·
              refine ⟨780718605602051204148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520479070401367469432243 780718605602051204148365)
              ·
                refine ⟨292769477100769201555637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780718605602051204148365 292769477100769201555637)
                ·
                  refine ⟨27447138478197112645841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292769477100769201555637 27447138478197112645841)
                  ·
                    rfl

theorem cell23_481078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_481078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481078 prefixEnd_481078 := by exact prefixLift 481078
  have htrace : WordTrace (prefixWord ++ tailWord_481078) baseStart_481078 baseEnd_481078 := by
    simpa [prefixWord, tailWord_481078, baseEnd_481078] using wordTrace_append hprefix tailTrace_481078
  have hstable : (prefixWord ++ tailWord_481078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481078).length < 2 ^ (prefixWord ++ tailWord_481078).sum := by decide
  have hdescent : baseEnd_481078 < baseStart_481078 := by decide
  rcases family_descends (prefixWord ++ tailWord_481078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481177 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_481177 : Nat := 118140960795 + 481177 * 2 ^ 59
def prefixEnd_481177 : Nat := 4983230072969 + 3 ^ 40 * 481177 * 2
def baseEnd_481177 : Nat := 82358360296189708824871

theorem tailTrace_481177 : CollatzResearch.WordTrace tailWord_481177 prefixEnd_481177 82358360296189708824871 := by
  unfold tailWord_481177
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549966977785382334145785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11699977985190254889430523 17549966977785382334145785)
  ·
    refine ⟨13162475233339036750609339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17549966977785382334145785 13162475233339036750609339)
    ·
      refine ⟨19743712850008555125914009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162475233339036750609339 19743712850008555125914009)
      ·
        refine ⟨14807784637506416344435507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19743712850008555125914009 14807784637506416344435507)
        ·
          refine ⟨22211676956259624516653261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807784637506416344435507 22211676956259624516653261)
          ·
            refine ⟨8329378858597359193744973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22211676956259624516653261 8329378858597359193744973)
            ·
              refine ⟨3123517071974009697654365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8329378858597359193744973 3123517071974009697654365)
              ·
                refine ⟨1171318901990253636620387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123517071974009697654365 1171318901990253636620387)
                ·
                  refine ⟨1756978352985380454930581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171318901990253636620387 1756978352985380454930581)
                  ·
                    refine ⟨82358360296189708824871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1756978352985380454930581 82358360296189708824871)
                    ·
                      rfl

theorem cell23_481177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_481177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481177 prefixEnd_481177 := by exact prefixLift 481177
  have htrace : WordTrace (prefixWord ++ tailWord_481177) baseStart_481177 baseEnd_481177 := by
    simpa [prefixWord, tailWord_481177, baseEnd_481177] using wordTrace_append hprefix tailTrace_481177
  have hstable : (prefixWord ++ tailWord_481177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481177).length < 2 ^ (prefixWord ++ tailWord_481177).sum := by decide
  have hdescent : baseEnd_481177 < baseStart_481177 := by decide
  rcases family_descends (prefixWord ++ tailWord_481177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481182 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_481182 : Nat := 118140960795 + 481182 * 2 ^ 59
def prefixEnd_481182 : Nat := 4983230072969 + 3 ^ 40 * 481182 * 2
def baseEnd_481182 : Nat := 247077648291841606912091

theorem tailTrace_481182 : CollatzResearch.WordTrace tailWord_481182 prefixEnd_481182 247077648291841606912091 := by
  unfold tailWord_481182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193768667845908523509725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11700099561844845458718533 2193768667845908523509725)
  ·
    refine ⟨822663250442215696316147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2193768667845908523509725 822663250442215696316147)
    ·
      refine ⟨1233994875663323544474221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822663250442215696316147 1233994875663323544474221)
      ·
        refine ⟨462748078373746329177833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1233994875663323544474221 462748078373746329177833)
        ·
          refine ⟨347061058780309746883375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462748078373746329177833 347061058780309746883375)
          ·
            refine ⟨520591588170464620325063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347061058780309746883375 520591588170464620325063)
            ·
              refine ⟨780887382255696930487595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520591588170464620325063 780887382255696930487595)
              ·
                refine ⟨1171331073383545395731393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780887382255696930487595 1171331073383545395731393)
                ·
                  refine ⟨878498305037659046798545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171331073383545395731393 878498305037659046798545)
                  ·
                    refine ⟨658873728778244285098909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 878498305037659046798545 658873728778244285098909)
                    ·
                      refine ⟨247077648291841606912091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 658873728778244285098909 247077648291841606912091)
                      ·
                        rfl

theorem cell23_481182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_481182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481182 prefixEnd_481182 := by exact prefixLift 481182
  have htrace : WordTrace (prefixWord ++ tailWord_481182) baseStart_481182 baseEnd_481182 := by
    simpa [prefixWord, tailWord_481182, baseEnd_481182] using wordTrace_append hprefix tailTrace_481182
  have hstable : (prefixWord ++ tailWord_481182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481182).length < 2 ^ (prefixWord ++ tailWord_481182).sum := by decide
  have hdescent : baseEnd_481182 < baseStart_481182 := by decide
  rcases family_descends (prefixWord ++ tailWord_481182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481184 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_481184 : Nat := 118140960795 + 481184 * 2 ^ 59
def prefixEnd_481184 : Nat := 4983230072969 + 3 ^ 40 * 481184 * 2
def baseEnd_481184 : Nat := 247078675253150599087081

theorem tailTrace_481184 : CollatzResearch.WordTrace tailWord_481184 prefixEnd_481184 247078675253150599087081 := by
  unfold tailWord_481184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775111144380011264825303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700148192506681686433737 8775111144380011264825303)
  ·
    refine ⟨13162666716570016897237955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775111144380011264825303 13162666716570016897237955)
    ·
      refine ⟨19744000074855025345856933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13162666716570016897237955 19744000074855025345856933)
      ·
        refine ⟨3702000014035317252348175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19744000074855025345856933 3702000014035317252348175)
        ·
          refine ⟨5553000021052975878522263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702000014035317252348175 5553000021052975878522263)
          ·
            refine ⟨8329500031579463817783395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553000021052975878522263 8329500031579463817783395)
            ·
              refine ⟨12494250047369195726675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329500031579463817783395 12494250047369195726675093)
              ·
                refine ⟨585667970970431049687895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12494250047369195726675093 585667970970431049687895)
                ·
                  refine ⟨878501956455646574531843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585667970970431049687895 878501956455646574531843)
                  ·
                    refine ⟨1317752934683469861797765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878501956455646574531843 1317752934683469861797765)
                    ·
                      refine ⟨247078675253150599087081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1317752934683469861797765 247078675253150599087081)
                      ·
                        rfl

theorem cell23_481184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_481184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481184 prefixEnd_481184 := by exact prefixLift 481184
  have htrace : WordTrace (prefixWord ++ tailWord_481184) baseStart_481184 baseEnd_481184 := by
    simpa [prefixWord, tailWord_481184, baseEnd_481184] using wordTrace_append hprefix tailTrace_481184
  have hstable : (prefixWord ++ tailWord_481184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481184).length < 2 ^ (prefixWord ++ tailWord_481184).sum := by decide
  have hdescent : baseEnd_481184 < baseStart_481184 := by decide
  rcases family_descends (prefixWord ++ tailWord_481184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481188 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_481188 : Nat := 118140960795 + 481188 * 2 ^ 59
def prefixEnd_481188 : Nat := 4983230072969 + 3 ^ 40 * 481188 * 2
def baseEnd_481188 : Nat := 247080729175768583437063

theorem tailTrace_481188 : CollatzResearch.WordTrace tailWord_481188 prefixEnd_481188 247080729175768583437063 := by
  unfold tailWord_481188
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775184090372765606398109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11700245453830354141864145 8775184090372765606398109)
  ·
    refine ⟨3290694033889787102399291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8775184090372765606398109 3290694033889787102399291)
    ·
      refine ⟨4936041050834680653598937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290694033889787102399291 4936041050834680653598937)
      ·
        refine ⟨3702030788126010490199203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4936041050834680653598937 3702030788126010490199203)
        ·
          refine ⟨5553046182189015735298805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702030788126010490199203 5553046182189015735298805)
          ·
            refine ⟨520598079580220225184263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5553046182189015735298805 520598079580220225184263)
            ·
              refine ⟨780897119370330337776395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520598079580220225184263 780897119370330337776395)
              ·
                refine ⟨1171345679055495506664593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780897119370330337776395 1171345679055495506664593)
                ·
                  refine ⟨878509259291621629998445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171345679055495506664593 878509259291621629998445)
                  ·
                    refine ⟨329440972234358111249417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878509259291621629998445 329440972234358111249417)
                    ·
                      refine ⟨247080729175768583437063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329440972234358111249417 247080729175768583437063)
                      ·
                        rfl

theorem cell23_481188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_481188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481188 prefixEnd_481188 := by exact prefixLift 481188
  have htrace : WordTrace (prefixWord ++ tailWord_481188) baseStart_481188 baseEnd_481188 := by
    simpa [prefixWord, tailWord_481188, baseEnd_481188] using wordTrace_append hprefix tailTrace_481188
  have hstable : (prefixWord ++ tailWord_481188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481188).length < 2 ^ (prefixWord ++ tailWord_481188).sum := by decide
  have hdescent : baseEnd_481188 < baseStart_481188 := by decide
  rcases family_descends (prefixWord ++ tailWord_481188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481201 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_481201 : Nat := 118140960795 + 481201 * 2 ^ 59
def prefixEnd_481201 : Nat := 4983230072969 + 3 ^ 40 * 481201 * 2
def baseEnd_481201 : Nat := 247087404424277032574503

theorem tailTrace_481201 : CollatzResearch.WordTrace tailWord_481201 prefixEnd_481201 247087404424277032574503 := by
  unfold tailWord_481201
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550842329698434433019457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11700561553132289622012971 17550842329698434433019457)
  ·
    refine ⟨13163131747273825824764593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17550842329698434433019457 13163131747273825824764593)
    ·
      refine ⟨9872348810455369368573445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13163131747273825824764593 9872348810455369368573445)
      ·
        refine ⟨1851065401960381756607521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9872348810455369368573445 1851065401960381756607521)
        ·
          refine ⟨1388299051470286317455641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851065401960381756607521 1388299051470286317455641)
          ·
            refine ⟨1041224288602714738091731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388299051470286317455641 1041224288602714738091731)
            ·
              refine ⟨1561836432904072107137597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041224288602714738091731 1561836432904072107137597)
              ·
                refine ⟨585688662339027040176599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561836432904072107137597 585688662339027040176599)
                ·
                  refine ⟨878532993508540560264899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585688662339027040176599 878532993508540560264899)
                  ·
                    refine ⟨1317799490262810840397349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878532993508540560264899 1317799490262810840397349)
                    ·
                      refine ⟨247087404424277032574503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1317799490262810840397349 247087404424277032574503)
                      ·
                        rfl

theorem cell23_481201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_481201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481201 prefixEnd_481201 := by exact prefixLift 481201
  have htrace : WordTrace (prefixWord ++ tailWord_481201) baseStart_481201 baseEnd_481201 := by
    simpa [prefixWord, tailWord_481201, baseEnd_481201] using wordTrace_append hprefix tailTrace_481201
  have hstable : (prefixWord ++ tailWord_481201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481201).length < 2 ^ (prefixWord ++ tailWord_481201).sum := by decide
  have hdescent : baseEnd_481201 < baseStart_481201 := by decide
  rcases family_descends (prefixWord ++ tailWord_481201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481228 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_481228 : Nat := 118140960795 + 481228 * 2 ^ 59
def prefixEnd_481228 : Nat := 4983230072969 + 3 ^ 40 * 481228 * 2
def baseEnd_481228 : Nat := 82367089467316142312293

theorem tailTrace_481228 : CollatzResearch.WordTrace tailWord_481228 prefixEnd_481228 82367089467316142312293 := by
  unfold tailWord_481228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775913550300309022126169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11701218067067078696168225 8775913550300309022126169)
  ·
    refine ⟨6581935162725231766594627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8775913550300309022126169 6581935162725231766594627)
    ·
      refine ⟨9872902744087847649891941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6581935162725231766594627 9872902744087847649891941)
      ·
        refine ⟨1851169264516471434354739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9872902744087847649891941 1851169264516471434354739)
        ·
          refine ⟨2776753896774707151532109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851169264516471434354739 2776753896774707151532109)
          ·
            refine ⟨1041282711290515181824541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2776753896774707151532109 1041282711290515181824541)
            ·
              refine ⟨390481016733943193184203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041282711290515181824541 390481016733943193184203)
              ·
                refine ⟨585721525100914789776305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390481016733943193184203 585721525100914789776305)
                ·
                  refine ⟨439291143825686092332229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585721525100914789776305 439291143825686092332229)
                  ·
                    refine ⟨82367089467316142312293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439291143825686092332229 82367089467316142312293)
                    ·
                      rfl

theorem cell23_481228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_481228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481228 prefixEnd_481228 := by exact prefixLift 481228
  have htrace : WordTrace (prefixWord ++ tailWord_481228) baseStart_481228 baseEnd_481228 := by
    simpa [prefixWord, tailWord_481228, baseEnd_481228] using wordTrace_append hprefix tailTrace_481228
  have hstable : (prefixWord ++ tailWord_481228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481228).length < 2 ^ (prefixWord ++ tailWord_481228).sum := by decide
  have hdescent : baseEnd_481228 < baseStart_481228 := by decide
  rcases family_descends (prefixWord ++ tailWord_481228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481241 : List Nat := [1, 2, 1, 2, 6, 2, 2, 7]
def baseStart_481241 : Nat := 118140960795 + 481241 * 2 ^ 59
def prefixEnd_481241 : Nat := 4983230072969 + 3 ^ 40 * 481241 * 2
def baseEnd_481241 : Nat := 9152146061128032447197

theorem tailTrace_481241 : CollatzResearch.WordTrace tailWord_481241 prefixEnd_481241 9152146061128032447197 := by
  unfold tailWord_481241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552301249553521264475577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11701534166369014176317051 17552301249553521264475577)
  ·
    refine ⟨13164225937165140948356683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17552301249553521264475577 13164225937165140948356683)
    ·
      refine ⟨19746338905747711422535025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13164225937165140948356683 19746338905747711422535025)
      ·
        refine ⟨14809754179310783566901269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19746338905747711422535025 14809754179310783566901269)
        ·
          refine ⟨694207227155192979698497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14809754179310783566901269 694207227155192979698497)
          ·
            refine ⟨520655420366394734773873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694207227155192979698497 520655420366394734773873)
            ·
              refine ⟨390491565274796051080405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520655420366394734773873 390491565274796051080405)
              ·
                refine ⟨9152146061128032447197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 390491565274796051080405 9152146061128032447197)
                ·
                  rfl

theorem cell23_481241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 7].length) (baseStart_481241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481241 prefixEnd_481241 := by exact prefixLift 481241
  have htrace : WordTrace (prefixWord ++ tailWord_481241) baseStart_481241 baseEnd_481241 := by
    simpa [prefixWord, tailWord_481241, baseEnd_481241] using wordTrace_append hprefix tailTrace_481241
  have hstable : (prefixWord ++ tailWord_481241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481241).length < 2 ^ (prefixWord ++ tailWord_481241).sum := by decide
  have hdescent : baseEnd_481241 < baseStart_481241 := by decide
  rcases family_descends (prefixWord ++ tailWord_481241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481251 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 3]
def baseStart_481251 : Nat := 118140960795 + 481251 * 2 ^ 59
def prefixEnd_481251 : Nat := 4983230072969 + 3 ^ 40 * 481251 * 2
def baseEnd_481251 : Nat := 247113078457001836949273

theorem tailTrace_481251 : CollatzResearch.WordTrace tailWord_481251 prefixEnd_481251 247113078457001836949273 := by
  unfold tailWord_481251
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552665979517292972339607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11701777319678195314893071 17552665979517292972339607)
  ·
    refine ⟨26328998969275939458509411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552665979517292972339607 26328998969275939458509411)
    ·
      refine ⟨39493498453913909187764117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328998969275939458509411 39493498453913909187764117)
      ·
        refine ⟨1851257740027214493176443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39493498453913909187764117 1851257740027214493176443)
        ·
          refine ⟨2776886610040821739764665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851257740027214493176443 2776886610040821739764665)
          ·
            refine ⟨2082664957530616304823499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776886610040821739764665 2082664957530616304823499)
            ·
              refine ⟨3123997436295924457235249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082664957530616304823499 3123997436295924457235249)
              ·
                refine ⟨2342998077221943342926437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3123997436295924457235249 2342998077221943342926437)
                ·
                  refine ⟨439312139479114376798707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2342998077221943342926437 439312139479114376798707)
                  ·
                    refine ⟨658968209218671565198061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439312139479114376798707 658968209218671565198061)
                    ·
                      refine ⟨247113078457001836949273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 658968209218671565198061 247113078457001836949273)
                      ·
                        rfl

theorem cell23_481251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_481251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481251 prefixEnd_481251 := by exact prefixLift 481251
  have htrace : WordTrace (prefixWord ++ tailWord_481251) baseStart_481251 baseEnd_481251 := by
    simpa [prefixWord, tailWord_481251, baseEnd_481251] using wordTrace_append hprefix tailTrace_481251
  have hstable : (prefixWord ++ tailWord_481251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481251).length < 2 ^ (prefixWord ++ tailWord_481251).sum := by decide
  have hdescent : baseEnd_481251 < baseStart_481251 := by decide
  rcases family_descends (prefixWord ++ tailWord_481251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481267 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 4, 6]
def baseStart_481267 : Nat := 118140960795 + 481267 * 2 ^ 59
def prefixEnd_481267 : Nat := 4983230072969 + 3 ^ 40 * 481267 * 2
def baseEnd_481267 : Nat := 82373764715824591449733

theorem tailTrace_481267 : CollatzResearch.WordTrace tailWord_481267 prefixEnd_481267 82373764715824591449733 := by
  unfold tailWord_481267
  simp only [CollatzResearch.WordTrace]
  refine ⟨17553249547459327704922055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11702166364972885136614703 17553249547459327704922055)
  ·
    refine ⟨26329874321188991557383083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17553249547459327704922055 26329874321188991557383083)
    ·
      refine ⟨39494811481783487336074625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26329874321188991557383083 39494811481783487336074625)
      ·
        refine ⟨29621108611337615502055969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39494811481783487336074625 29621108611337615502055969)
        ·
          refine ⟨22215831458503211626541977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29621108611337615502055969 22215831458503211626541977)
          ·
            refine ⟨16661873593877408719906483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22215831458503211626541977 16661873593877408719906483)
            ·
              refine ⟨24992810390816113079859725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661873593877408719906483 24992810390816113079859725)
              ·
                refine ⟨9372303896556042404947397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24992810390816113079859725 9372303896556042404947397)
                ·
                  refine ⟨1757306980604257950927637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9372303896556042404947397 1757306980604257950927637)
                  ·
                    refine ⟨82373764715824591449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1757306980604257950927637 82373764715824591449733)
                    ·
                      rfl

theorem cell23_481267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_481267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481267 prefixEnd_481267 := by exact prefixLift 481267
  have htrace : WordTrace (prefixWord ++ tailWord_481267) baseStart_481267 baseEnd_481267 := by
    simpa [prefixWord, tailWord_481267, baseEnd_481267] using wordTrace_append hprefix tailTrace_481267
  have hstable : (prefixWord ++ tailWord_481267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481267).length < 2 ^ (prefixWord ++ tailWord_481267).sum := by decide
  have hdescent : baseEnd_481267 < baseStart_481267 := by decide
  rcases family_descends (prefixWord ++ tailWord_481267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481285 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_481285 : Nat := 118140960795 + 481285 * 2 ^ 59
def prefixEnd_481285 : Nat := 4983230072969 + 3 ^ 40 * 481285 * 2
def baseEnd_481285 : Nat := 247130536799254703924117

theorem tailTrace_481285 : CollatzResearch.WordTrace tailWord_481285 prefixEnd_481285 247130536799254703924117 := by
  unfold tailWord_481285
  simp only [CollatzResearch.WordTrace]
  refine ⟨17553906061394116779077309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11702604040929411186051539 17553906061394116779077309)
  ·
    refine ⟨6582714773022793792153991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17553906061394116779077309 6582714773022793792153991)
    ·
      refine ⟨9874072159534190688230987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6582714773022793792153991 9874072159534190688230987)
      ·
        refine ⟨14811108239301286032346481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874072159534190688230987 14811108239301286032346481)
        ·
          refine ⟨11108331179475964524259861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14811108239301286032346481 11108331179475964524259861)
          ·
            refine ⟨520703024037935837074681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11108331179475964524259861 520703024037935837074681)
            ·
              refine ⟨390527268028451877806011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520703024037935837074681 390527268028451877806011)
              ·
                refine ⟨585790902042677816709017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390527268028451877806011 585790902042677816709017)
                ·
                  refine ⟨439343176532008362531763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585790902042677816709017 439343176532008362531763)
                  ·
                    refine ⟨659014764798012543797645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439343176532008362531763 659014764798012543797645)
                    ·
                      refine ⟨247130536799254703924117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 659014764798012543797645 247130536799254703924117)
                      ·
                        rfl

theorem cell23_481285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_481285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481285 prefixEnd_481285 := by exact prefixLift 481285
  have htrace : WordTrace (prefixWord ++ tailWord_481285) baseStart_481285 baseEnd_481285 := by
    simpa [prefixWord, tailWord_481285, baseEnd_481285] using wordTrace_append hprefix tailTrace_481285
  have hstable : (prefixWord ++ tailWord_481285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481285).length < 2 ^ (prefixWord ++ tailWord_481285).sum := by decide
  have hdescent : baseEnd_481285 < baseStart_481285 := by decide
  rcases family_descends (prefixWord ++ tailWord_481285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481286 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_481286 : Nat := 118140960795 + 481286 * 2 ^ 59
def prefixEnd_481286 : Nat := 4983230072969 + 3 ^ 40 * 481286 * 2
def baseEnd_481286 : Nat := 247131050279909200011613

theorem tailTrace_481286 : CollatzResearch.WordTrace tailWord_481286 prefixEnd_481286 247131050279909200011613 := by
  unfold tailWord_481286
  simp only [CollatzResearch.WordTrace]
  refine ⟨548560704199702935933241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11702628356260329299909141 548560704199702935933241)
  ·
    refine ⟨411420528149777201949931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 548560704199702935933241 411420528149777201949931)
    ·
      refine ⟨617130792224665802924897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411420528149777201949931 617130792224665802924897)
      ·
        refine ⟨462848094168499352193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617130792224665802924897 462848094168499352193673)
        ·
          refine ⟨347136070626374514145255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462848094168499352193673 347136070626374514145255)
          ·
            refine ⟨520704105939561771217883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347136070626374514145255 520704105939561771217883)
            ·
              refine ⟨781056158909342656826825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520704105939561771217883 781056158909342656826825)
              ·
                refine ⟨585792119182006992620119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781056158909342656826825 585792119182006992620119)
                ·
                  refine ⟨878688178773010488930179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585792119182006992620119 878688178773010488930179)
                  ·
                    refine ⟨1318032268159515733395269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 878688178773010488930179 1318032268159515733395269)
                    ·
                      refine ⟨247131050279909200011613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1318032268159515733395269 247131050279909200011613)
                      ·
                        rfl

theorem cell23_481286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_481286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481286 prefixEnd_481286 := by exact prefixLift 481286
  have htrace : WordTrace (prefixWord ++ tailWord_481286) baseStart_481286 baseEnd_481286 := by
    simpa [prefixWord, tailWord_481286, baseEnd_481286] using wordTrace_append hprefix tailTrace_481286
  have hstable : (prefixWord ++ tailWord_481286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481286).length < 2 ^ (prefixWord ++ tailWord_481286).sum := by decide
  have hdescent : baseEnd_481286 < baseStart_481286 := by decide
  rcases family_descends (prefixWord ++ tailWord_481286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_481291 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 4, 2]
def baseStart_481291 : Nat := 118140960795 + 481291 * 2 ^ 59
def prefixEnd_481291 : Nat := 4983230072969 + 3 ^ 40 * 481291 * 2
def baseEnd_481291 : Nat := 247133617683181680449089

theorem tailTrace_481291 : CollatzResearch.WordTrace tailWord_481291 prefixEnd_481291 247133617683181680449089 := by
  unfold tailWord_481291
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554124899372379803795727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11702749932914919869197151 17554124899372379803795727)
  ·
    refine ⟨26331187349058569705693591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554124899372379803795727 26331187349058569705693591)
    ·
      refine ⟨39496781023587854558540387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26331187349058569705693591 39496781023587854558540387)
      ·
        refine ⟨59245171535381781837810581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39496781023587854558540387 59245171535381781837810581)
        ·
          refine ⟨2777117415721021023647371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59245171535381781837810581 2777117415721021023647371)
          ·
            refine ⟨4165676123581531535471057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777117415721021023647371 4165676123581531535471057)
            ·
              refine ⟨3124257092686148651603293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4165676123581531535471057 3124257092686148651603293)
              ·
                refine ⟨1171596409757305744351235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124257092686148651603293 1171596409757305744351235)
                ·
                  refine ⟨1757394614635958616526853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171596409757305744351235 1757394614635958616526853)
                  ·
                    refine ⟨329511490244242240598785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757394614635958616526853 329511490244242240598785)
                    ·
                      refine ⟨247133617683181680449089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 329511490244242240598785 247133617683181680449089)
                      ·
                        rfl

theorem cell23_481291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4, 2].length) (baseStart_481291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_481291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_481291 prefixEnd_481291 := by exact prefixLift 481291
  have htrace : WordTrace (prefixWord ++ tailWord_481291) baseStart_481291 baseEnd_481291 := by
    simpa [prefixWord, tailWord_481291, baseEnd_481291] using wordTrace_append hprefix tailTrace_481291
  have hstable : (prefixWord ++ tailWord_481291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_481291).length < 2 ^ (prefixWord ++ tailWord_481291).sum := by decide
  have hdescent : baseEnd_481291 < baseStart_481291 := by decide
  rcases family_descends (prefixWord ++ tailWord_481291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
