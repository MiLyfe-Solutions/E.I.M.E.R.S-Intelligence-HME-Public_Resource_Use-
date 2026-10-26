import V185TrunkScan23Chunk0494

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2928174 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_2928174 : Nat := 118140960795 + 2928174 * 2 ^ 59
def prefixEnd_2928174 : Nat := 4983230072969 + 3 ^ 40 * 2928174 * 2
def baseEnd_2928174 : Nat := 501186900666177246486193

theorem tailTrace_2928174 : CollatzResearch.WordTrace tailWord_2928174 prefixEnd_2928174 501186900666177246486193 := by
  unfold tailWord_2928174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349909961716645643740947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71199519795822110099951717 13349909961716645643740947)
  ·
    refine ⟨20024864942574968465611421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349909961716645643740947 20024864942574968465611421)
    ·
      refine ⟨7509324353465613174604283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20024864942574968465611421 7509324353465613174604283)
      ·
        refine ⟨11263986530198419761906425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7509324353465613174604283 11263986530198419761906425)
        ·
          refine ⟨8447989897648814821429819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11263986530198419761906425 8447989897648814821429819)
          ·
            refine ⟨12671984846473222232144729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447989897648814821429819 12671984846473222232144729)
            ·
              refine ⟨9503988634854916674108547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12671984846473222232144729 9503988634854916674108547)
              ·
                refine ⟨14255982952282375011162821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9503988634854916674108547 14255982952282375011162821)
                ·
                  refine ⟨2672996803552945314593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14255982952282375011162821 2672996803552945314593029)
                  ·
                    refine ⟨501186900666177246486193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672996803552945314593029 501186900666177246486193)
                    ·
                      rfl

theorem cell23_2928174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_2928174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928174 prefixEnd_2928174 := by exact prefixLift 2928174
  have htrace : WordTrace (prefixWord ++ tailWord_2928174) baseStart_2928174 baseEnd_2928174 := by
    simpa [prefixWord, tailWord_2928174, baseEnd_2928174] using wordTrace_append hprefix tailTrace_2928174
  have hstable : (prefixWord ++ tailWord_2928174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928174).length < 2 ^ (prefixWord ++ tailWord_2928174).sum := by decide
  have hdescent : baseEnd_2928174 < baseStart_2928174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928181 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_2928181 : Nat := 118140960795 + 2928181 * 2 ^ 59
def prefixEnd_2928181 : Nat := 4983230072969 + 3 ^ 40 * 2928181 * 2
def baseEnd_2928181 : Nat := 1503564296363113212071047

theorem tailTrace_2928181 : CollatzResearch.WordTrace tailWord_2928181 prefixEnd_2928181 1503564296363113212071047 := by
  unfold tailWord_2928181
  simp only [CollatzResearch.WordTrace]
  refine ⟨106799535004707805345432397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71199690003138536896954931 106799535004707805345432397)
  ·
    refine ⟨40049825626765427004537149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106799535004707805345432397 40049825626765427004537149)
    ·
      refine ⟨15018684610037035126701431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40049825626765427004537149 15018684610037035126701431)
      ·
        refine ⟨22528026915055552690052147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15018684610037035126701431 22528026915055552690052147)
        ·
          refine ⟨33792040372583329035078221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22528026915055552690052147 33792040372583329035078221)
          ·
            refine ⟨12672015139718748388154333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33792040372583329035078221 12672015139718748388154333)
            ·
              refine ⟨4752005677394530645557875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12672015139718748388154333 4752005677394530645557875)
              ·
                refine ⟨7128008516091795968336813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752005677394530645557875 7128008516091795968336813)
                ·
                  refine ⟨2673003193534423488126305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7128008516091795968336813 2673003193534423488126305)
                  ·
                    refine ⟨2004752395150817616094729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673003193534423488126305 2004752395150817616094729)
                    ·
                      refine ⟨1503564296363113212071047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004752395150817616094729 1503564296363113212071047)
                      ·
                        rfl

theorem cell23_2928181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_2928181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928181 prefixEnd_2928181 := by exact prefixLift 2928181
  have htrace : WordTrace (prefixWord ++ tailWord_2928181) baseStart_2928181 baseEnd_2928181 := by
    simpa [prefixWord, tailWord_2928181, baseEnd_2928181] using wordTrace_append hprefix tailTrace_2928181
  have hstable : (prefixWord ++ tailWord_2928181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928181).length < 2 ^ (prefixWord ++ tailWord_2928181).sum := by decide
  have hdescent : baseEnd_2928181 < baseStart_2928181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928191 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 2, 4]
def baseStart_2928191 : Nat := 118140960795 + 2928191 * 2 ^ 59
def prefixEnd_2928191 : Nat := 4983230072969 + 3 ^ 40 * 2928191 * 2
def baseEnd_2928191 : Nat := 501189810389886057648667

theorem tailTrace_2928191 : CollatzResearch.WordTrace tailWord_2928191 prefixEnd_2928191 501189810389886057648667 := by
  unfold tailWord_2928191
  simp only [CollatzResearch.WordTrace]
  refine ⟨106799899734671577053296427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71199933156447718035530951 106799899734671577053296427)
  ·
    refine ⟨160199849602007365579944641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106799899734671577053296427 160199849602007365579944641)
    ·
      refine ⟨120149887201505524184958481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160199849602007365579944641 120149887201505524184958481)
      ·
        refine ⟨90112415401129143138718861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120149887201505524184958481 90112415401129143138718861)
        ·
          refine ⟨33792155775423428677019573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90112415401129143138718861 33792155775423428677019573)
          ·
            refine ⟨3168014603945946438470585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33792155775423428677019573 3168014603945946438470585)
            ·
              refine ⟨2376010952959459828852939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168014603945946438470585 2376010952959459828852939)
              ·
                refine ⟨3564016429439189743279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376010952959459828852939 3564016429439189743279409)
                ·
                  refine ⟨2673012322079392307459557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564016429439189743279409 2673012322079392307459557)
                  ·
                    refine ⟨501189810389886057648667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673012322079392307459557 501189810389886057648667)
                    ·
                      rfl

theorem cell23_2928191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_2928191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928191 prefixEnd_2928191 := by exact prefixLift 2928191
  have htrace : WordTrace (prefixWord ++ tailWord_2928191) baseStart_2928191 baseEnd_2928191 := by
    simpa [prefixWord, tailWord_2928191, baseEnd_2928191] using wordTrace_append hprefix tailTrace_2928191
  have hstable : (prefixWord ++ tailWord_2928191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928191).length < 2 ^ (prefixWord ++ tailWord_2928191).sum := by decide
  have hdescent : baseEnd_2928191 < baseStart_2928191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928197 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_2928197 : Nat := 118140960795 + 2928197 * 2 ^ 59
def prefixEnd_2928197 : Nat := 4983230072969 + 3 ^ 40 * 2928197 * 2
def baseEnd_2928197 : Nat := 1503572512053585149470973

theorem tailTrace_2928197 : CollatzResearch.WordTrace tailWord_2928197 prefixEnd_2928197 1503572512053585149470973 := by
  unfold tailWord_2928197
  simp only [CollatzResearch.WordTrace]
  refine ⟨106800118572649840078014845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71200079048433226718676563 106800118572649840078014845)
  ·
    refine ⟨40050044464743690029255567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106800118572649840078014845 40050044464743690029255567)
    ·
      refine ⟨60075066697115535043883351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40050044464743690029255567 60075066697115535043883351)
      ·
        refine ⟨90112600045673302565825027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60075066697115535043883351 90112600045673302565825027)
        ·
          refine ⟨135168900068509953848737541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90112600045673302565825027 135168900068509953848737541)
          ·
            refine ⟨25344168762845616346638289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135168900068509953848737541 25344168762845616346638289)
            ·
              refine ⟨19008126572134212259978717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25344168762845616346638289 19008126572134212259978717)
              ·
                refine ⟨7128047464550329597492019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19008126572134212259978717 7128047464550329597492019)
                ·
                  refine ⟨10692071196825494396238029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128047464550329597492019 10692071196825494396238029)
                  ·
                    refine ⟨4009526698809560398589261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10692071196825494396238029 4009526698809560398589261)
                    ·
                      refine ⟨1503572512053585149470973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009526698809560398589261 1503572512053585149470973)
                      ·
                        rfl

theorem cell23_2928197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_2928197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928197 prefixEnd_2928197 := by exact prefixLift 2928197
  have htrace : WordTrace (prefixWord ++ tailWord_2928197) baseStart_2928197 baseEnd_2928197 := by
    simpa [prefixWord, tailWord_2928197, baseEnd_2928197] using wordTrace_append hprefix tailTrace_2928197
  have hstable : (prefixWord ++ tailWord_2928197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928197).length < 2 ^ (prefixWord ++ tailWord_2928197).sum := by decide
  have hdescent : baseEnd_2928197 < baseStart_2928197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928232 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2928232 : Nat := 118140960795 + 2928232 * 2 ^ 59
def prefixEnd_2928232 : Nat := 4983230072969 + 3 ^ 40 * 2928232 * 2
def baseEnd_2928232 : Nat := 1503590483876492512533313

theorem tailTrace_2928232 : CollatzResearch.WordTrace tailWord_2928232 prefixEnd_2928232 1503590483876492512533313 := by
  unfold tailWord_2928232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53400697563761520527769475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71200930085015360703692633 53400697563761520527769475)
  ·
    refine ⟨80101046345642280791654213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53400697563761520527769475 80101046345642280791654213)
    ·
      refine ⟨15018946189807927648435165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80101046345642280791654213 15018946189807927648435165)
      ·
        refine ⟨5632104821177972868163187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15018946189807927648435165 5632104821177972868163187)
        ·
          refine ⟨8448157231766959302244781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632104821177972868163187 8448157231766959302244781)
          ·
            refine ⟨3168058961912609738341793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8448157231766959302244781 3168058961912609738341793)
            ·
              refine ⟨2376044221434457303756345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168058961912609738341793 2376044221434457303756345)
              ·
                refine ⟨1782033166075842977817259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376044221434457303756345 1782033166075842977817259)
                ·
                  refine ⟨2673049749113764466725889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782033166075842977817259 2673049749113764466725889)
                  ·
                    refine ⟨2004787311835323350044417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673049749113764466725889 2004787311835323350044417)
                    ·
                      refine ⟨1503590483876492512533313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004787311835323350044417 1503590483876492512533313)
                      ·
                        rfl

theorem cell23_2928232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2928232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928232 prefixEnd_2928232 := by exact prefixLift 2928232
  have htrace : WordTrace (prefixWord ++ tailWord_2928232) baseStart_2928232 baseEnd_2928232 := by
    simpa [prefixWord, tailWord_2928232, baseEnd_2928232] using wordTrace_append hprefix tailTrace_2928232
  have hstable : (prefixWord ++ tailWord_2928232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928232).length < 2 ^ (prefixWord ++ tailWord_2928232).sum := by decide
  have hdescent : baseEnd_2928232 < baseStart_2928232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928288 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2]
def baseStart_2928288 : Nat := 118140960795 + 2928288 * 2 ^ 59
def prefixEnd_2928288 : Nat := 4983230072969 + 3 ^ 40 * 2928288 * 2
def baseEnd_2928288 : Nat := 1503619238793144293433055

theorem tailTrace_2928288 : CollatzResearch.WordTrace tailWord_2928288 prefixEnd_2928288 1503619238793144293433055 := by
  unfold tailWord_2928288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53401718807660081309788759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71202291743546775079718345 53401718807660081309788759)
  ·
    refine ⟨80102578211490121964683139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53401718807660081309788759 80102578211490121964683139)
    ·
      refine ⟨120153867317235182947024709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80102578211490121964683139 120153867317235182947024709)
      ·
        refine ⟨22528850121981596802567133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120153867317235182947024709 22528850121981596802567133)
        ·
          refine ⟨8448318795743098800962675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22528850121981596802567133 8448318795743098800962675)
          ·
            refine ⟨12672478193614648201444013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448318795743098800962675 12672478193614648201444013)
            ·
              refine ⟨4752179322605493075541505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12672478193614648201444013 4752179322605493075541505)
              ·
                refine ⟨3564134491954119806656129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752179322605493075541505 3564134491954119806656129)
                ·
                  refine ⟨2673100868965589854992097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564134491954119806656129 2673100868965589854992097)
                  ·
                    refine ⟨2004825651724192391244073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673100868965589854992097 2004825651724192391244073)
                    ·
                      refine ⟨1503619238793144293433055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004825651724192391244073 1503619238793144293433055)
                      ·
                        rfl

theorem cell23_2928288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_2928288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928288 prefixEnd_2928288 := by exact prefixLift 2928288
  have htrace : WordTrace (prefixWord ++ tailWord_2928288) baseStart_2928288 baseEnd_2928288 := by
    simpa [prefixWord, tailWord_2928288, baseEnd_2928288] using wordTrace_append hprefix tailTrace_2928288
  have hstable : (prefixWord ++ tailWord_2928288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928288).length < 2 ^ (prefixWord ++ tailWord_2928288).sum := by decide
  have hdescent : baseEnd_2928288 < baseStart_2928288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928324 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2928324 : Nat := 118140960795 + 2928324 * 2 ^ 59
def prefixEnd_2928324 : Nat := 4983230072969 + 3 ^ 40 * 2928324 * 2
def baseEnd_2928324 : Nat := 501212574698902050860963

theorem tailTrace_2928324 : CollatzResearch.WordTrace tailWord_2928324 prefixEnd_2928324 501212574698902050860963 := by
  unfold tailWord_2928324
  simp only [CollatzResearch.WordTrace]
  refine ⟨53402375321594870383944013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71203167095459827178592017 53402375321594870383944013)
  ·
    refine ⟨20025890745598076393979005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53402375321594870383944013 20025890745598076393979005)
    ·
      refine ⟨7509709029599278647742127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20025890745598076393979005 7509709029599278647742127)
      ·
        refine ⟨11264563544398917971613191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7509709029599278647742127 11264563544398917971613191)
        ·
          refine ⟨16896845316598376957419787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11264563544398917971613191 16896845316598376957419787)
          ·
            refine ⟨25345267974897565436129681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16896845316598376957419787 25345267974897565436129681)
            ·
              refine ⟨19008950981173174077097261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25345267974897565436129681 19008950981173174077097261)
              ·
                refine ⟨7128356617939940278911473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19008950981173174077097261 7128356617939940278911473)
                ·
                  refine ⟨5346267463454955209183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128356617939940278911473 5346267463454955209183605)
                  ·
                    refine ⟨501212574698902050860963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5346267463454955209183605 501212574698902050860963)
                    ·
                      rfl

theorem cell23_2928324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2928324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928324 prefixEnd_2928324 := by exact prefixLift 2928324
  have htrace : WordTrace (prefixWord ++ tailWord_2928324) baseStart_2928324 baseEnd_2928324 := by
    simpa [prefixWord, tailWord_2928324, baseEnd_2928324] using wordTrace_append hprefix tailTrace_2928324
  have hstable : (prefixWord ++ tailWord_2928324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928324).length < 2 ^ (prefixWord ++ tailWord_2928324).sum := by decide
  have hdescent : baseEnd_2928324 < baseStart_2928324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928327 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2928327 : Nat := 118140960795 + 2928327 * 2 ^ 59
def prefixEnd_2928327 : Nat := 4983230072969 + 3 ^ 40 * 2928327 * 2
def baseEnd_2928327 : Nat := 1503639264538669640845375

theorem tailTrace_2928327 : CollatzResearch.WordTrace tailWord_2928327 prefixEnd_2928327 1503639264538669640845375 := by
  unfold tailWord_2928327
  simp only [CollatzResearch.WordTrace]
  refine ⟨106804860062178872280247235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71203240041452581520164823 106804860062178872280247235)
  ·
    refine ⟨160207290093268308420370853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106804860062178872280247235 160207290093268308420370853)
    ·
      refine ⟨30038866892487807828819535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160207290093268308420370853 30038866892487807828819535)
      ·
        refine ⟨45058300338731711743229303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30038866892487807828819535 45058300338731711743229303)
        ·
          refine ⟨67587450508097567614843955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45058300338731711743229303 67587450508097567614843955)
          ·
            refine ⟨101381175762146351422265933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67587450508097567614843955 101381175762146351422265933)
            ·
              refine ⟨38017940910804881783349725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101381175762146351422265933 38017940910804881783349725)
              ·
                refine ⟨14256727841551830668756147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38017940910804881783349725 14256727841551830668756147)
                ·
                  refine ⟨21385091762327746003134221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14256727841551830668756147 21385091762327746003134221)
                  ·
                    refine ⟨8019409410872904751175333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21385091762327746003134221 8019409410872904751175333)
                    ·
                      refine ⟨1503639264538669640845375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8019409410872904751175333 1503639264538669640845375)
                      ·
                        rfl

theorem cell23_2928327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2928327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928327 prefixEnd_2928327 := by exact prefixLift 2928327
  have htrace : WordTrace (prefixWord ++ tailWord_2928327) baseStart_2928327 baseEnd_2928327 := by
    simpa [prefixWord, tailWord_2928327, baseEnd_2928327] using wordTrace_append hprefix tailTrace_2928327
  have hstable : (prefixWord ++ tailWord_2928327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928327).length < 2 ^ (prefixWord ++ tailWord_2928327).sum := by decide
  have hdescent : baseEnd_2928327 < baseStart_2928327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928344 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2928344 : Nat := 118140960795 + 2928344 * 2 ^ 59
def prefixEnd_2928344 : Nat := 4983230072969 + 3 ^ 40 * 2928344 * 2
def baseEnd_2928344 : Nat := 1503647993709796074332797

theorem tailTrace_2928344 : CollatzResearch.WordTrace tailWord_2928344 prefixEnd_2928344 1503647993709796074332797 := by
  unfold tailWord_2928344
  simp only [CollatzResearch.WordTrace]
  refine ⟨53402740051558642091808043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71203653402078189455744057 53402740051558642091808043)
  ·
    refine ⟨80104110077337963137712065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53402740051558642091808043 80104110077337963137712065)
    ·
      refine ⟨60078082558003472353284049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80104110077337963137712065 60078082558003472353284049)
      ·
        refine ⟨45058561918502604264963037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60078082558003472353284049 45058561918502604264963037)
        ·
          refine ⟨16896960719438476599361139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45058561918502604264963037 16896960719438476599361139)
          ·
            refine ⟨25345441079157714899041709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16896960719438476599361139 25345441079157714899041709)
            ·
              refine ⟨9504540404684143087140641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25345441079157714899041709 9504540404684143087140641)
              ·
                refine ⟨7128405303513107315355481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504540404684143087140641 7128405303513107315355481)
                ·
                  refine ⟨5346303977634830486516611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128405303513107315355481 5346303977634830486516611)
                  ·
                    refine ⟨8019455966452245729774917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5346303977634830486516611 8019455966452245729774917)
                    ·
                      refine ⟨1503647993709796074332797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8019455966452245729774917 1503647993709796074332797)
                      ·
                        rfl

theorem cell23_2928344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2928344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928344 prefixEnd_2928344 := by exact prefixLift 2928344
  have htrace : WordTrace (prefixWord ++ tailWord_2928344) baseStart_2928344 baseEnd_2928344 := by
    simpa [prefixWord, tailWord_2928344, baseEnd_2928344] using wordTrace_append hprefix tailTrace_2928344
  have hstable : (prefixWord ++ tailWord_2928344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928344).length < 2 ^ (prefixWord ++ tailWord_2928344).sum := by decide
  have hdescent : baseEnd_2928344 < baseStart_2928344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928405 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2928405 : Nat := 118140960795 + 2928405 * 2 ^ 59
def prefixEnd_2928405 : Nat := 4983230072969 + 3 ^ 40 * 2928405 * 2
def baseEnd_2928405 : Nat := 501226438676573445223339

theorem tailTrace_2928405 : CollatzResearch.WordTrace tailWord_2928405 prefixEnd_2928405 501226438676573445223339 := by
  unfold tailWord_2928405
  simp only [CollatzResearch.WordTrace]
  refine ⟨106807704955896291601586669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71205136637264194401057779 106807704955896291601586669)
  ·
    refine ⟨40052889358461109350595001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106807704955896291601586669 40052889358461109350595001)
    ·
      refine ⟨30039667018845832012946251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40052889358461109350595001 30039667018845832012946251)
      ·
        refine ⟨45059500528268748019419377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30039667018845832012946251 45059500528268748019419377)
        ·
          refine ⟨33794625396201561014564533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45059500528268748019419377 33794625396201561014564533)
          ·
            refine ⟨3168246130893896345115425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33794625396201561014564533 3168246130893896345115425)
            ·
              refine ⟨2376184598170422258836569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168246130893896345115425 2376184598170422258836569)
              ·
                refine ⟨1782138448627816694127427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376184598170422258836569 1782138448627816694127427)
                ·
                  refine ⟨2673207672941725041191141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782138448627816694127427 2673207672941725041191141)
                  ·
                    refine ⟨501226438676573445223339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673207672941725041191141 501226438676573445223339)
                    ·
                      rfl

theorem cell23_2928405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2928405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928405 prefixEnd_2928405 := by exact prefixLift 2928405
  have htrace : WordTrace (prefixWord ++ tailWord_2928405) baseStart_2928405 baseEnd_2928405 := by
    simpa [prefixWord, tailWord_2928405, baseEnd_2928405] using wordTrace_append hprefix tailTrace_2928405
  have hstable : (prefixWord ++ tailWord_2928405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928405).length < 2 ^ (prefixWord ++ tailWord_2928405).sum := by decide
  have hdescent : baseEnd_2928405 < baseStart_2928405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928444 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2928444 : Nat := 118140960795 + 2928444 * 2 ^ 59
def prefixEnd_2928444 : Nat := 4983230072969 + 3 ^ 40 * 2928444 * 2
def baseEnd_2928444 : Nat := 501233113925081894360779

theorem tailTrace_2928444 : CollatzResearch.WordTrace tailWord_2928444 prefixEnd_2928444 501233113925081894360779 := by
  unfold tailWord_2928444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53404563701377500631128193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71206084935170000841504257 53404563701377500631128193)
  ·
    refine ⟨40053422776033125473346145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53404563701377500631128193 40053422776033125473346145)
    ·
      refine ⟨30040067082024844105009609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40053422776033125473346145 30040067082024844105009609)
      ·
        refine ⟨22530050311518633078757207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30040067082024844105009609 22530050311518633078757207)
        ·
          refine ⟨33795075467277949618135811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22530050311518633078757207 33795075467277949618135811)
          ·
            refine ⟨50692613200916924427203717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33795075467277949618135811 50692613200916924427203717)
            ·
              refine ⟨9504864975171923330100697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50692613200916924427203717 9504864975171923330100697)
              ·
                refine ⟨7128648731378942497575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504864975171923330100697 7128648731378942497575523)
                ·
                  refine ⟨10692973097068413746363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128648731378942497575523 10692973097068413746363285)
                  ·
                    refine ⟨501233113925081894360779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10692973097068413746363285 501233113925081894360779)
                    ·
                      rfl

theorem cell23_2928444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2928444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928444 prefixEnd_2928444 := by exact prefixLift 2928444
  have htrace : WordTrace (prefixWord ++ tailWord_2928444) baseStart_2928444 baseEnd_2928444 := by
    simpa [prefixWord, tailWord_2928444, baseEnd_2928444] using wordTrace_append hprefix tailTrace_2928444
  have hstable : (prefixWord ++ tailWord_2928444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928444).length < 2 ^ (prefixWord ++ tailWord_2928444).sum := by decide
  have hdescent : baseEnd_2928444 < baseStart_2928444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928445 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2928445 : Nat := 118140960795 + 2928445 * 2 ^ 59
def prefixEnd_2928445 : Nat := 4983230072969 + 3 ^ 40 * 2928445 * 2
def baseEnd_2928445 : Nat := 1503699855255900179169833

theorem tailTrace_2928445 : CollatzResearch.WordTrace tailWord_2928445 prefixEnd_2928445 1503699855255900179169833 := by
  unfold tailWord_2928445
  simp only [CollatzResearch.WordTrace]
  refine ⟨106809163875751378433042789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71206109250500918955361859 106809163875751378433042789)
  ·
    refine ⟨20026718226703383456195523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106809163875751378433042789 20026718226703383456195523)
    ·
      refine ⟨30040077340055075184293285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20026718226703383456195523 30040077340055075184293285)
      ·
        refine ⟨5632514501260326597054991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30040077340055075184293285 5632514501260326597054991)
        ·
          refine ⟨8448771751890489895582487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632514501260326597054991 8448771751890489895582487)
          ·
            refine ⟨12673157627835734843373731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448771751890489895582487 12673157627835734843373731)
            ·
              refine ⟨19009736441753602265060597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12673157627835734843373731 19009736441753602265060597)
              ·
                refine ⟨1782162791414400212349431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19009736441753602265060597 1782162791414400212349431)
                ·
                  refine ⟨2673244187121600318524147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782162791414400212349431 2673244187121600318524147)
                  ·
                    refine ⟨4009866280682400477786221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2673244187121600318524147 4009866280682400477786221)
                    ·
                      refine ⟨1503699855255900179169833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009866280682400477786221 1503699855255900179169833)
                      ·
                        rfl

theorem cell23_2928445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2928445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928445 prefixEnd_2928445 := by exact prefixLift 2928445
  have htrace : WordTrace (prefixWord ++ tailWord_2928445) baseStart_2928445 baseEnd_2928445 := by
    simpa [prefixWord, tailWord_2928445, baseEnd_2928445] using wordTrace_append hprefix tailTrace_2928445
  have hstable : (prefixWord ++ tailWord_2928445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928445).length < 2 ^ (prefixWord ++ tailWord_2928445).sum := by decide
  have hdescent : baseEnd_2928445 < baseStart_2928445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928451 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 4]
def baseStart_2928451 : Nat := 118140960795 + 2928451 * 2 ^ 59
def prefixEnd_2928451 : Nat := 4983230072969 + 3 ^ 40 * 2928451 * 2
def baseEnd_2928451 : Nat := 1503702936139827155694805

theorem tailTrace_2928451 : CollatzResearch.WordTrace tailWord_2928451 prefixEnd_2928451 1503702936139827155694805 := by
  unfold tailWord_2928451
  simp only [CollatzResearch.WordTrace]
  refine ⟨106809382713729641457761207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71206255142486427638507471 106809382713729641457761207)
  ·
    refine ⟨160214074070594462186641811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106809382713729641457761207 160214074070594462186641811)
    ·
      refine ⟨240321111105891693279962717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160214074070594462186641811 240321111105891693279962717)
      ·
        refine ⟨90120416664709384979986019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240321111105891693279962717 90120416664709384979986019)
        ·
          refine ⟨135180624997064077469979029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90120416664709384979986019 135180624997064077469979029)
          ·
            refine ⟨6336591796737378631405267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135180624997064077469979029 6336591796737378631405267)
            ·
              refine ⟨9504887695106067947107901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336591796737378631405267 9504887695106067947107901)
              ·
                refine ⟨3564332885664775480165463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9504887695106067947107901 3564332885664775480165463)
                ·
                  refine ⟨5346499328497163220248195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564332885664775480165463 5346499328497163220248195)
                  ·
                    refine ⟨8019748992745744830372293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5346499328497163220248195 8019748992745744830372293)
                    ·
                      refine ⟨1503702936139827155694805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8019748992745744830372293 1503702936139827155694805)
                      ·
                        rfl

theorem cell23_2928451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_2928451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928451 prefixEnd_2928451 := by exact prefixLift 2928451
  have htrace : WordTrace (prefixWord ++ tailWord_2928451) baseStart_2928451 baseEnd_2928451 := by
    simpa [prefixWord, tailWord_2928451, baseEnd_2928451] using wordTrace_append hprefix tailTrace_2928451
  have hstable : (prefixWord ++ tailWord_2928451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928451).length < 2 ^ (prefixWord ++ tailWord_2928451).sum := by decide
  have hdescent : baseEnd_2928451 < baseStart_2928451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928457 : List Nat := [1, 2, 1, 1, 2, 4, 12]
def baseStart_2928457 : Nat := 118140960795 + 2928457 * 2 ^ 59
def prefixEnd_2928457 : Nat := 4983230072969 + 3 ^ 40 * 2928457 * 2
def baseEnd_2928457 : Nat := 18564271815108075706417

theorem tailTrace_2928457 : CollatzResearch.WordTrace tailWord_2928457 prefixEnd_2928457 18564271815108075706417 := by
  unfold tailWord_2928457
  simp only [CollatzResearch.WordTrace]
  refine ⟨106809601551707904482479625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71206401034471936321653083 106809601551707904482479625)
  ·
    refine ⟨80107201163780928361859719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106809601551707904482479625 80107201163780928361859719)
    ·
      refine ⟨120160801745671392542789579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80107201163780928361859719 120160801745671392542789579)
      ·
        refine ⟨180241202618507088814184369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120160801745671392542789579 180241202618507088814184369)
        ·
          refine ⟨135180901963880316610638277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180241202618507088814184369 135180901963880316610638277)
          ·
            refine ⟨25346419118227559364494677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135180901963880316610638277 25346419118227559364494677)
            ·
              refine ⟨18564271815108075706417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25346419118227559364494677 18564271815108075706417)
              ·
                rfl

theorem cell23_2928457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 12].length) (baseStart_2928457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928457 prefixEnd_2928457 := by exact prefixLift 2928457
  have htrace : WordTrace (prefixWord ++ tailWord_2928457) baseStart_2928457 baseEnd_2928457 := by
    simpa [prefixWord, tailWord_2928457, baseEnd_2928457] using wordTrace_append hprefix tailTrace_2928457
  have hstable : (prefixWord ++ tailWord_2928457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928457).length < 2 ^ (prefixWord ++ tailWord_2928457).sum := by decide
  have hdescent : baseEnd_2928457 < baseStart_2928457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928467 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_2928467 : Nat := 118140960795 + 2928467 * 2 ^ 59
def prefixEnd_2928467 : Nat := 4983230072969 + 3 ^ 40 * 2928467 * 2
def baseEnd_2928467 : Nat := 1503711151830299093094731

theorem tailTrace_2928467 : CollatzResearch.WordTrace tailWord_2928467 prefixEnd_2928467 1503711151830299093094731 := by
  unfold tailWord_2928467
  simp only [CollatzResearch.WordTrace]
  refine ⟨106809966281671676190343655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71206644187781117460229103 106809966281671676190343655)
  ·
    refine ⟨160214949422507514285515483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106809966281671676190343655 160214949422507514285515483)
    ·
      refine ⟨240322424133761271428273225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160214949422507514285515483 240322424133761271428273225)
      ·
        refine ⟨180241818100320953571204919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240322424133761271428273225 180241818100320953571204919)
        ·
          refine ⟨270362727150481430356807379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180241818100320953571204919 270362727150481430356807379)
          ·
            refine ⟨405544090725722145535211069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270362727150481430356807379 405544090725722145535211069)
            ·
              refine ⟨152079034022145804575704151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405544090725722145535211069 152079034022145804575704151)
              ·
                refine ⟨228118551033218706863556227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152079034022145804575704151 228118551033218706863556227)
                ·
                  refine ⟨342177826549828060295334341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228118551033218706863556227 342177826549828060295334341)
                  ·
                    refine ⟨64158342478092761305375189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 342177826549828060295334341 64158342478092761305375189)
                    ·
                      refine ⟨1503711151830299093094731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64158342478092761305375189 1503711151830299093094731)
                      ·
                        rfl

theorem cell23_2928467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_2928467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928467 prefixEnd_2928467 := by exact prefixLift 2928467
  have htrace : WordTrace (prefixWord ++ tailWord_2928467) baseStart_2928467 baseEnd_2928467 := by
    simpa [prefixWord, tailWord_2928467, baseEnd_2928467] using wordTrace_append hprefix tailTrace_2928467
  have hstable : (prefixWord ++ tailWord_2928467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928467).length < 2 ^ (prefixWord ++ tailWord_2928467).sum := by decide
  have hdescent : baseEnd_2928467 < baseStart_2928467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928471 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_2928471 : Nat := 118140960795 + 2928471 * 2 ^ 59
def prefixEnd_2928471 : Nat := 4983230072969 + 3 ^ 40 * 2928471 * 2
def baseEnd_2928471 : Nat := 1503713205752917077444713

theorem tailTrace_2928471 : CollatzResearch.WordTrace tailWord_2928471 prefixEnd_2928471 1503713205752917077444713 := by
  unfold tailWord_2928471
  simp only [CollatzResearch.WordTrace]
  refine ⟨106810112173657184873489267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71206741449104789915659511 106810112173657184873489267)
  ·
    refine ⟨160215168260485777310233901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106810112173657184873489267 160215168260485777310233901)
    ·
      refine ⟨60080688097682166491337713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160215168260485777310233901 60080688097682166491337713)
      ·
        refine ⟨45060516073261624868503285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60080688097682166491337713 45060516073261624868503285)
        ·
          refine ⟨4224423381868277331422183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45060516073261624868503285 4224423381868277331422183)
          ·
            refine ⟨6336635072802415997133275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224423381868277331422183 6336635072802415997133275)
            ·
              refine ⟨9504952609203623995699913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336635072802415997133275 9504952609203623995699913)
              ·
                refine ⟨7128714456902717996774935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504952609203623995699913 7128714456902717996774935)
                ·
                  refine ⟨10693071685354076995162403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128714456902717996774935 10693071685354076995162403)
                  ·
                    refine ⟨16039607528031115492743605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693071685354076995162403 16039607528031115492743605)
                    ·
                      refine ⟨1503713205752917077444713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16039607528031115492743605 1503713205752917077444713)
                      ·
                        rfl

theorem cell23_2928471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_2928471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928471 prefixEnd_2928471 := by exact prefixLift 2928471
  have htrace : WordTrace (prefixWord ++ tailWord_2928471) baseStart_2928471 baseEnd_2928471 := by
    simpa [prefixWord, tailWord_2928471, baseEnd_2928471] using wordTrace_append hprefix tailTrace_2928471
  have hstable : (prefixWord ++ tailWord_2928471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928471).length < 2 ^ (prefixWord ++ tailWord_2928471).sum := by decide
  have hdescent : baseEnd_2928471 < baseStart_2928471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928488 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2928488 : Nat := 118140960795 + 2928488 * 2 ^ 59
def prefixEnd_2928488 : Nat := 4983230072969 + 3 ^ 40 * 2928488 * 2
def baseEnd_2928488 : Nat := 1503721934924043510932135

theorem tailTrace_2928488 : CollatzResearch.WordTrace tailWord_2928488 prefixEnd_2928488 1503721934924043510932135 := by
  unfold tailWord_2928488
  simp only [CollatzResearch.WordTrace]
  refine ⟨53405366107297798388429059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71207154809730397851238745 53405366107297798388429059)
  ·
    refine ⟨80108049160946697582643589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53405366107297798388429059 80108049160946697582643589)
    ·
      refine ⟨15020259217677505796745673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80108049160946697582643589 15020259217677505796745673)
      ·
        refine ⟨11265194413258129347559255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15020259217677505796745673 11265194413258129347559255)
        ·
          refine ⟨16897791619887194021338883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265194413258129347559255 16897791619887194021338883)
          ·
            refine ⟨25346687429830791032008325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16897791619887194021338883 25346687429830791032008325)
            ·
              refine ⟨4752503893093273318501561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25346687429830791032008325 4752503893093273318501561)
              ·
                refine ⟨3564377919819954988876171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752503893093273318501561 3564377919819954988876171)
                ·
                  refine ⟨5346566879729932483314257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564377919819954988876171 5346566879729932483314257)
                  ·
                    refine ⟨4009925159797449362485693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5346566879729932483314257 4009925159797449362485693)
                    ·
                      refine ⟨1503721934924043510932135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009925159797449362485693 1503721934924043510932135)
                      ·
                        rfl

theorem cell23_2928488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2928488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928488 prefixEnd_2928488 := by exact prefixLift 2928488
  have htrace : WordTrace (prefixWord ++ tailWord_2928488) baseStart_2928488 baseEnd_2928488 := by
    simpa [prefixWord, tailWord_2928488, baseEnd_2928488] using wordTrace_append hprefix tailTrace_2928488
  have hstable : (prefixWord ++ tailWord_2928488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928488).length < 2 ^ (prefixWord ++ tailWord_2928488).sum := by decide
  have hdescent : baseEnd_2928488 < baseStart_2928488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928501 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2928501 : Nat := 118140960795 + 2928501 * 2 ^ 59
def prefixEnd_2928501 : Nat := 4983230072969 + 3 ^ 40 * 2928501 * 2
def baseEnd_2928501 : Nat := 1503728610172551960069575

theorem tailTrace_2928501 : CollatzResearch.WordTrace tailWord_2928501 prefixEnd_2928501 1503728610172551960069575 := by
  unfold tailWord_2928501
  simp only [CollatzResearch.WordTrace]
  refine ⟨106811206363548499997081357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71207470909032333331387571 106811206363548499997081357)
  ·
    refine ⟨40054202386330687498905509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106811206363548499997081357 40054202386330687498905509)
    ·
      refine ⟨7510162947437003906044783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40054202386330687498905509 7510162947437003906044783)
      ·
        refine ⟨11265244421155505859067175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510162947437003906044783 11265244421155505859067175)
        ·
          refine ⟨16897866631733258788600763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265244421155505859067175 16897866631733258788600763)
          ·
            refine ⟨25346799947599888182901145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16897866631733258788600763 25346799947599888182901145)
            ·
              refine ⟨19010099960699916137175859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25346799947599888182901145 19010099960699916137175859)
              ·
                refine ⟨28515149941049874205763789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19010099960699916137175859 28515149941049874205763789)
                ·
                  refine ⟨10693181227893702827161421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28515149941049874205763789 10693181227893702827161421)
                  ·
                    refine ⟨4009942960460138560185533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10693181227893702827161421 4009942960460138560185533)
                    ·
                      refine ⟨1503728610172551960069575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009942960460138560185533 1503728610172551960069575)
                      ·
                        rfl

theorem cell23_2928501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2928501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928501 prefixEnd_2928501 := by exact prefixLift 2928501
  have htrace : WordTrace (prefixWord ++ tailWord_2928501) baseStart_2928501 baseEnd_2928501 := by
    simpa [prefixWord, tailWord_2928501, baseEnd_2928501] using wordTrace_append hprefix tailTrace_2928501
  have hstable : (prefixWord ++ tailWord_2928501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928501).length < 2 ^ (prefixWord ++ tailWord_2928501).sum := by decide
  have hdescent : baseEnd_2928501 < baseStart_2928501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928511 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 5, 3, 2]
def baseStart_2928511 : Nat := 118140960795 + 2928511 * 2 ^ 59
def prefixEnd_2928511 : Nat := 4983230072969 + 3 ^ 40 * 2928511 * 2
def baseEnd_2928511 : Nat := 1503733744979096920944529

theorem tailTrace_2928511 : CollatzResearch.WordTrace tailWord_2928511 prefixEnd_2928511 1503733744979096920944529 := by
  unfold tailWord_2928511
  simp only [CollatzResearch.WordTrace]
  refine ⟨106811571093512271704945387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71207714062341514469963591 106811571093512271704945387)
  ·
    refine ⟨160217356640268407557418081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106811571093512271704945387 160217356640268407557418081)
    ·
      refine ⟨120163017480201305668063561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160217356640268407557418081 120163017480201305668063561)
      ·
        refine ⟨90122263110150979251047671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120163017480201305668063561 90122263110150979251047671)
        ·
          refine ⟨135183394665226468876571507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90122263110150979251047671 135183394665226468876571507)
          ·
            refine ⟨202775091997839703314857261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135183394665226468876571507 202775091997839703314857261)
            ·
              refine ⟨76040659499189888743071473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202775091997839703314857261 76040659499189888743071473)
              ·
                refine ⟨57030494624392416557303605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76040659499189888743071473 57030494624392416557303605)
                ·
                  refine ⟨5346608871036789052247213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57030494624392416557303605 5346608871036789052247213)
                  ·
                    refine ⟨2004978326638795894592705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5346608871036789052247213 2004978326638795894592705)
                    ·
                      refine ⟨1503733744979096920944529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004978326638795894592705 1503733744979096920944529)
                      ·
                        rfl

theorem cell23_2928511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_2928511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928511 prefixEnd_2928511 := by exact prefixLift 2928511
  have htrace : WordTrace (prefixWord ++ tailWord_2928511) baseStart_2928511 baseEnd_2928511 := by
    simpa [prefixWord, tailWord_2928511, baseEnd_2928511] using wordTrace_append hprefix tailTrace_2928511
  have hstable : (prefixWord ++ tailWord_2928511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928511).length < 2 ^ (prefixWord ++ tailWord_2928511).sum := by decide
  have hdescent : baseEnd_2928511 < baseStart_2928511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928519 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_2928519 : Nat := 118140960795 + 2928519 * 2 ^ 59
def prefixEnd_2928519 : Nat := 4983230072969 + 3 ^ 40 * 2928519 * 2
def baseEnd_2928519 : Nat := 1503737852824332889644493

theorem tailTrace_2928519 : CollatzResearch.WordTrace tailWord_2928519 prefixEnd_2928519 1503737852824332889644493 := by
  unfold tailWord_2928519
  simp only [CollatzResearch.WordTrace]
  refine ⟨106811862877483289071236611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71207908584988859380824407 106811862877483289071236611)
  ·
    refine ⟨160217794316224933606854917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106811862877483289071236611 160217794316224933606854917)
    ·
      refine ⟨30040836434292175051285297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160217794316224933606854917 30040836434292175051285297)
      ·
        refine ⟨22530627325719131288463973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30040836434292175051285297 22530627325719131288463973)
        ·
          refine ⟨4224492623572337116586995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22530627325719131288463973 4224492623572337116586995)
          ·
            refine ⟨6336738935358505674880493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224492623572337116586995 6336738935358505674880493)
            ·
              refine ⟨2376277100759439628080185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6336738935358505674880493 2376277100759439628080185)
              ·
                refine ⟨1782207825569579721060139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376277100759439628080185 1782207825569579721060139)
                ·
                  refine ⟨2673311738354369581590209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782207825569579721060139 2673311738354369581590209)
                  ·
                    refine ⟨2004983803765777186192657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673311738354369581590209 2004983803765777186192657)
                    ·
                      refine ⟨1503737852824332889644493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2004983803765777186192657 1503737852824332889644493)
                      ·
                        rfl

theorem cell23_2928519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_2928519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928519 prefixEnd_2928519 := by exact prefixLift 2928519
  have htrace : WordTrace (prefixWord ++ tailWord_2928519) baseStart_2928519 baseEnd_2928519 := by
    simpa [prefixWord, tailWord_2928519, baseEnd_2928519] using wordTrace_append hprefix tailTrace_2928519
  have hstable : (prefixWord ++ tailWord_2928519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928519).length < 2 ^ (prefixWord ++ tailWord_2928519).sum := by decide
  have hdescent : baseEnd_2928519 < baseStart_2928519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928524 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2928524 : Nat := 118140960795 + 2928524 * 2 ^ 59
def prefixEnd_2928524 : Nat := 4983230072969 + 3 ^ 40 * 2928524 * 2
def baseEnd_2928524 : Nat := 1503740420227605370081969

theorem tailTrace_2928524 : CollatzResearch.WordTrace tailWord_2928524 prefixEnd_2928524 1503740420227605370081969 := by
  unfold tailWord_2928524
  simp only [CollatzResearch.WordTrace]
  refine ⟨53406022621232587462584313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71208030161643449950112417 53406022621232587462584313)
  ·
    refine ⟨40054516965924440596938235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53406022621232587462584313 40054516965924440596938235)
    ·
      refine ⟨60081775448886660895407353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054516965924440596938235 60081775448886660895407353)
      ·
        refine ⟨45061331586664995671555515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60081775448886660895407353 45061331586664995671555515)
        ·
          refine ⟨67591997379997493507333273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45061331586664995671555515 67591997379997493507333273)
          ·
            refine ⟨50693998034998120130499955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67591997379997493507333273 50693998034998120130499955)
            ·
              refine ⟨76040997052497180195749933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50693998034998120130499955 76040997052497180195749933)
              ·
                refine ⟨28515373894686442573406225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76040997052497180195749933 28515373894686442573406225)
                ·
                  refine ⟨21386530421014831930054669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28515373894686442573406225 21386530421014831930054669)
                  ·
                    refine ⟨8019948907880561973770501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21386530421014831930054669 8019948907880561973770501)
                    ·
                      refine ⟨1503740420227605370081969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8019948907880561973770501 1503740420227605370081969)
                      ·
                        rfl

theorem cell23_2928524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2928524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928524 prefixEnd_2928524 := by exact prefixLift 2928524
  have htrace : WordTrace (prefixWord ++ tailWord_2928524) baseStart_2928524 baseEnd_2928524 := by
    simpa [prefixWord, tailWord_2928524, baseEnd_2928524] using wordTrace_append hprefix tailTrace_2928524
  have hstable : (prefixWord ++ tailWord_2928524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928524).length < 2 ^ (prefixWord ++ tailWord_2928524).sum := by decide
  have hdescent : baseEnd_2928524 < baseStart_2928524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928535 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2928535 : Nat := 118140960795 + 2928535 * 2 ^ 59
def prefixEnd_2928535 : Nat := 4983230072969 + 3 ^ 40 * 2928535 * 2
def baseEnd_2928535 : Nat := 1503746068514804827044419

theorem tailTrace_2928535 : CollatzResearch.WordTrace tailWord_2928535 prefixEnd_2928535 1503746068514804827044419 := by
  unfold tailWord_2928535
  simp only [CollatzResearch.WordTrace]
  refine ⟨106812446445425323803819059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71208297630283549202546039 106812446445425323803819059)
  ·
    refine ⟨160218669668137985705728589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106812446445425323803819059 160218669668137985705728589)
    ·
      refine ⟨60082001125551744639648221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160218669668137985705728589 60082001125551744639648221)
      ·
        refine ⟨22530750422081904239868083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60082001125551744639648221 22530750422081904239868083)
        ·
          refine ⟨33796125633122856359802125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22530750422081904239868083 33796125633122856359802125)
          ·
            refine ⟨12673547112421071134925797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33796125633122856359802125 12673547112421071134925797)
            ·
              refine ⟨2376290083578950837798587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12673547112421071134925797 2376290083578950837798587)
              ·
                refine ⟨3564435125368426256697881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376290083578950837798587 3564435125368426256697881)
                ·
                  refine ⟨2673326344026319692523411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564435125368426256697881 2673326344026319692523411)
                  ·
                    refine ⟨4009989516039479538785117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2673326344026319692523411 4009989516039479538785117)
                    ·
                      refine ⟨1503746068514804827044419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4009989516039479538785117 1503746068514804827044419)
                      ·
                        rfl

theorem cell23_2928535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2928535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928535 prefixEnd_2928535 := by exact prefixLift 2928535
  have htrace : WordTrace (prefixWord ++ tailWord_2928535) baseStart_2928535 baseEnd_2928535 := by
    simpa [prefixWord, tailWord_2928535, baseEnd_2928535] using wordTrace_append hprefix tailTrace_2928535
  have hstable : (prefixWord ++ tailWord_2928535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928535).length < 2 ^ (prefixWord ++ tailWord_2928535).sum := by decide
  have hdescent : baseEnd_2928535 < baseStart_2928535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928545 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2928545 : Nat := 118140960795 + 2928545 * 2 ^ 59
def prefixEnd_2928545 : Nat := 4983230072969 + 3 ^ 40 * 2928545 * 2
def baseEnd_2928545 : Nat := 1503751203321349787919373

theorem tailTrace_2928545 : CollatzResearch.WordTrace tailWord_2928545 prefixEnd_2928545 1503751203321349787919373 := by
  unfold tailWord_2928545
  simp only [CollatzResearch.WordTrace]
  refine ⟨106812811175389095511683089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71208540783592730341122059 106812811175389095511683089)
  ·
    refine ⟨80109608381541821633762317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106812811175389095511683089 80109608381541821633762317)
    ·
      refine ⟨30041103143078183112660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80109608381541821633762317 30041103143078183112660869)
      ·
        refine ⟨5632706839327159333623913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30041103143078183112660869 5632706839327159333623913)
        ·
          refine ⟨4224530129495369500217935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5632706839327159333623913 4224530129495369500217935)
          ·
            refine ⟨6336795194243054250326903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224530129495369500217935 6336795194243054250326903)
            ·
              refine ⟨9505192791364581375490355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336795194243054250326903 9505192791364581375490355)
              ·
                refine ⟨14257789187046872063235533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505192791364581375490355 14257789187046872063235533)
                ·
                  refine ⟨5346670945142577023713325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14257789187046872063235533 5346670945142577023713325)
                  ·
                    refine ⟨2005001604428466383892497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5346670945142577023713325 2005001604428466383892497)
                    ·
                      refine ⟨1503751203321349787919373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005001604428466383892497 1503751203321349787919373)
                      ·
                        rfl

theorem cell23_2928545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2928545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928545 prefixEnd_2928545 := by exact prefixLift 2928545
  have htrace : WordTrace (prefixWord ++ tailWord_2928545) baseStart_2928545 baseEnd_2928545 := by
    simpa [prefixWord, tailWord_2928545, baseEnd_2928545] using wordTrace_append hprefix tailTrace_2928545
  have hstable : (prefixWord ++ tailWord_2928545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928545).length < 2 ^ (prefixWord ++ tailWord_2928545).sum := by decide
  have hdescent : baseEnd_2928545 < baseStart_2928545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928561 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2928561 : Nat := 118140960795 + 2928561 * 2 ^ 59
def prefixEnd_2928561 : Nat := 4983230072969 + 3 ^ 40 * 2928561 * 2
def baseEnd_2928561 : Nat := 1503759419011821725319299

theorem tailTrace_2928561 : CollatzResearch.WordTrace tailWord_2928561 prefixEnd_2928561 1503759419011821725319299 := by
  unfold tailWord_2928561
  simp only [CollatzResearch.WordTrace]
  refine ⟨106813394743331130244265537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71208929828887420162843691 106813394743331130244265537)
  ·
    refine ⟨80110046057498347683199153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106813394743331130244265537 80110046057498347683199153)
    ·
      refine ⟨60082534543123760762399365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80110046057498347683199153 60082534543123760762399365)
      ·
        refine ⟨11265475226835705142949881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60082534543123760762399365 11265475226835705142949881)
        ·
          refine ⟨8449106420126778857212411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11265475226835705142949881 8449106420126778857212411)
          ·
            refine ⟨12673659630190168285818617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8449106420126778857212411 12673659630190168285818617)
            ·
              refine ⟨9505244722642626214363963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12673659630190168285818617 9505244722642626214363963)
              ·
                refine ⟨14257867083963939321545945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505244722642626214363963 14257867083963939321545945)
                ·
                  refine ⟨10693400312972954491159459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14257867083963939321545945 10693400312972954491159459)
                  ·
                    refine ⟨16040100469459431736739189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693400312972954491159459 16040100469459431736739189)
                    ·
                      refine ⟨1503759419011821725319299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16040100469459431736739189 1503759419011821725319299)
                      ·
                        rfl

theorem cell23_2928561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2928561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928561 prefixEnd_2928561 := by exact prefixLift 2928561
  have htrace : WordTrace (prefixWord ++ tailWord_2928561) baseStart_2928561 baseEnd_2928561 := by
    simpa [prefixWord, tailWord_2928561, baseEnd_2928561] using wordTrace_append hprefix tailTrace_2928561
  have hstable : (prefixWord ++ tailWord_2928561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928561).length < 2 ^ (prefixWord ++ tailWord_2928561).sum := by decide
  have hdescent : baseEnd_2928561 < baseStart_2928561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928575 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 2, 2, 2]
def baseStart_2928575 : Nat := 118140960795 + 2928575 * 2 ^ 59
def prefixEnd_2928575 : Nat := 4983230072969 + 3 ^ 40 * 2928575 * 2
def baseEnd_2928575 : Nat := 1503766607740984670544235

theorem tailTrace_2928575 : CollatzResearch.WordTrace tailWord_2928575 prefixEnd_2928575 1503766607740984670544235 := by
  unfold tailWord_2928575
  simp only [CollatzResearch.WordTrace]
  refine ⟨106813905365280410635275179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71209270243520273756850119 106813905365280410635275179)
  ·
    refine ⟨160220858047920615952912769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106813905365280410635275179 160220858047920615952912769)
    ·
      refine ⟨120165643535940461964684577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160220858047920615952912769 120165643535940461964684577)
      ·
        refine ⟨90124232651955346473513433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120165643535940461964684577 90124232651955346473513433)
        ·
          refine ⟨67593174488966509855135075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90124232651955346473513433 67593174488966509855135075)
          ·
            refine ⟨101389761733449764782702613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67593174488966509855135075 101389761733449764782702613)
            ·
              refine ⟨4752645081255457724189185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101389761733449764782702613 4752645081255457724189185)
              ·
                refine ⟨3564483810941593293141889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752645081255457724189185 3564483810941593293141889)
                ·
                  refine ⟨2673362858206194969856417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564483810941593293141889 2673362858206194969856417)
                  ·
                    refine ⟨2005022143654646227392313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673362858206194969856417 2005022143654646227392313)
                    ·
                      refine ⟨1503766607740984670544235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005022143654646227392313 1503766607740984670544235)
                      ·
                        rfl

theorem cell23_2928575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_2928575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928575 prefixEnd_2928575 := by exact prefixLift 2928575
  have htrace : WordTrace (prefixWord ++ tailWord_2928575) baseStart_2928575 baseEnd_2928575 := by
    simpa [prefixWord, tailWord_2928575, baseEnd_2928575] using wordTrace_append hprefix tailTrace_2928575
  have hstable : (prefixWord ++ tailWord_2928575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928575).length < 2 ^ (prefixWord ++ tailWord_2928575).sum := by decide
  have hdescent : baseEnd_2928575 < baseStart_2928575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928591 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_2928591 : Nat := 118140960795 + 2928591 * 2 ^ 59
def prefixEnd_2928591 : Nat := 4983230072969 + 3 ^ 40 * 2928591 * 2
def baseEnd_2928591 : Nat := 1503774823431456607944161

theorem tailTrace_2928591 : CollatzResearch.WordTrace tailWord_2928591 prefixEnd_2928591 1503774823431456607944161 := by
  unfold tailWord_2928591
  simp only [CollatzResearch.WordTrace]
  refine ⟨106814488933222445367857627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71209659288814963578571751 106814488933222445367857627)
  ·
    refine ⟨160221733399833668051786441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106814488933222445367857627 160221733399833668051786441)
    ·
      refine ⟨120166300049875251038839831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160221733399833668051786441 120166300049875251038839831)
      ·
        refine ⟨180249450074812876558259747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120166300049875251038839831 180249450074812876558259747)
        ·
          refine ⟨270374175112219314837389621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180249450074812876558259747 270374175112219314837389621)
          ·
            refine ⟨25347578916770560766005277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270374175112219314837389621 25347578916770560766005277)
            ·
              refine ⟨9505342093788960287251979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25347578916770560766005277 9505342093788960287251979)
              ·
                refine ⟨14258013140683440430877969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505342093788960287251979 14258013140683440430877969)
                ·
                  refine ⟨10693509855512580323158477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14258013140683440430877969 10693509855512580323158477)
                  ·
                    refine ⟨4010066195817217621184429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10693509855512580323158477 4010066195817217621184429)
                    ·
                      refine ⟨1503774823431456607944161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010066195817217621184429 1503774823431456607944161)
                      ·
                        rfl

theorem cell23_2928591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_2928591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928591 prefixEnd_2928591 := by exact prefixLift 2928591
  have htrace : WordTrace (prefixWord ++ tailWord_2928591) baseStart_2928591 baseEnd_2928591 := by
    simpa [prefixWord, tailWord_2928591, baseEnd_2928591] using wordTrace_append hprefix tailTrace_2928591
  have hstable : (prefixWord ++ tailWord_2928591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928591).length < 2 ^ (prefixWord ++ tailWord_2928591).sum := by decide
  have hdescent : baseEnd_2928591 < baseStart_2928591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928611 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 7]
def baseStart_2928611 : Nat := 118140960795 + 2928611 * 2 ^ 59
def prefixEnd_2928611 : Nat := 4983230072969 + 3 ^ 40 * 2928611 * 2
def baseEnd_2928611 : Nat := 501261697681515509898023

theorem tailTrace_2928611 : CollatzResearch.WordTrace tailWord_2928611 prefixEnd_2928611 501261697681515509898023 := by
  unfold tailWord_2928611
  simp only [CollatzResearch.WordTrace]
  refine ⟨106815218393149988783585687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71210145595433325855723791 106815218393149988783585687)
  ·
    refine ⟨160222827589724983175378531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106815218393149988783585687 160222827589724983175378531)
    ·
      refine ⟨240334241384587474763067797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160222827589724983175378531 240334241384587474763067797)
      ·
        refine ⟨11265667564902537879518803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240334241384587474763067797 11265667564902537879518803)
        ·
          refine ⟨16898501347353806819278205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265667564902537879518803 16898501347353806819278205)
          ·
            refine ⟨6336938005257677557229327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16898501347353806819278205 6336938005257677557229327)
            ·
              refine ⟨9505407007886516335843991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336938005257677557229327 9505407007886516335843991)
              ·
                refine ⟨14258110511829774503765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505407007886516335843991 14258110511829774503765987)
                ·
                  refine ⟨21387165767744661755648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14258110511829774503765987 21387165767744661755648981)
                  ·
                    refine ⟨501261697681515509898023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21387165767744661755648981 501261697681515509898023)
                    ·
                      rfl

theorem cell23_2928611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_2928611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928611 prefixEnd_2928611 := by exact prefixLift 2928611
  have htrace : WordTrace (prefixWord ++ tailWord_2928611) baseStart_2928611 baseEnd_2928611 := by
    simpa [prefixWord, tailWord_2928611, baseEnd_2928611] using wordTrace_append hprefix tailTrace_2928611
  have hstable : (prefixWord ++ tailWord_2928611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928611).length < 2 ^ (prefixWord ++ tailWord_2928611).sum := by decide
  have hdescent : baseEnd_2928611 < baseStart_2928611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928615 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 5]
def baseStart_2928615 : Nat := 118140960795 + 2928615 * 2 ^ 59
def prefixEnd_2928615 : Nat := 4983230072969 + 3 ^ 40 * 2928615 * 2
def baseEnd_2928615 : Nat := 167087460774129390449339

theorem tailTrace_2928615 : CollatzResearch.WordTrace tailWord_2928615 prefixEnd_2928615 167087460774129390449339 := by
  unfold tailWord_2928615
  simp only [CollatzResearch.WordTrace]
  refine ⟨106815364285135497466731299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71210242856756998311154199 106815364285135497466731299)
  ·
    refine ⟨160223046427703246200096949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106815364285135497466731299 160223046427703246200096949)
    ·
      refine ⟨15020910602597179331259089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160223046427703246200096949 15020910602597179331259089)
      ·
        refine ⟨11265682951947884498444317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15020910602597179331259089 11265682951947884498444317)
        ·
          refine ⟨4224631106980456686916619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11265682951947884498444317 4224631106980456686916619)
          ·
            refine ⟨6336946660470685030374929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224631106980456686916619 6336946660470685030374929)
            ·
              refine ⟨4752709995353013772781197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336946660470685030374929 4752709995353013772781197)
              ·
                refine ⟨1782266248257380164792949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4752709995353013772781197 1782266248257380164792949)
                ·
                  refine ⟨167087460774129390449339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782266248257380164792949 167087460774129390449339)
                  ·
                    rfl

theorem cell23_2928615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 5].length) (baseStart_2928615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928615 prefixEnd_2928615 := by exact prefixLift 2928615
  have htrace : WordTrace (prefixWord ++ tailWord_2928615) baseStart_2928615 baseEnd_2928615 := by
    simpa [prefixWord, tailWord_2928615, baseEnd_2928615] using wordTrace_append hprefix tailTrace_2928615
  have hstable : (prefixWord ++ tailWord_2928615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928615).length < 2 ^ (prefixWord ++ tailWord_2928615).sum := by decide
  have hdescent : baseEnd_2928615 < baseStart_2928615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928648 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_2928648 : Nat := 118140960795 + 2928648 * 2 ^ 59
def prefixEnd_2928648 : Nat := 4983230072969 + 3 ^ 40 * 2928648 * 2
def baseEnd_2928648 : Nat := 1503804091828762884931399

theorem tailTrace_2928648 : CollatzResearch.WordTrace tailWord_2928648 prefixEnd_2928648 1503804091828762884931399 := by
  unfold tailWord_2928648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53408283947007972051341299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71211045262677296068455065 53408283947007972051341299)
  ·
    refine ⟨80112425920511958077011949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53408283947007972051341299 80112425920511958077011949)
    ·
      refine ⟨30042159720191984278879481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80112425920511958077011949 30042159720191984278879481)
      ·
        refine ⟨22531619790143988209159611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30042159720191984278879481 22531619790143988209159611)
        ·
          refine ⟨33797429685215982313739417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22531619790143988209159611 33797429685215982313739417)
          ·
            refine ⟨25348072263911986735304563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33797429685215982313739417 25348072263911986735304563)
            ·
              refine ⟨38022108395867980102956845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25348072263911986735304563 38022108395867980102956845)
              ·
                refine ⟨14258290648450492538608817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38022108395867980102956845 14258290648450492538608817)
                ·
                  refine ⟨10693717986337869403956613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14258290648450492538608817 10693717986337869403956613)
                  ·
                    refine ⟨2005072122438350513241865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10693717986337869403956613 2005072122438350513241865)
                    ·
                      refine ⟨1503804091828762884931399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005072122438350513241865 1503804091828762884931399)
                      ·
                        rfl

theorem cell23_2928648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_2928648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928648 prefixEnd_2928648 := by exact prefixLift 2928648
  have htrace : WordTrace (prefixWord ++ tailWord_2928648) baseStart_2928648 baseEnd_2928648 := by
    simpa [prefixWord, tailWord_2928648, baseEnd_2928648] using wordTrace_append hprefix tailTrace_2928648
  have hstable : (prefixWord ++ tailWord_2928648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928648).length < 2 ^ (prefixWord ++ tailWord_2928648).sum := by decide
  have hdescent : baseEnd_2928648 < baseStart_2928648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928651 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3]
def baseStart_2928651 : Nat := 118140960795 + 2928651 * 2 ^ 59
def prefixEnd_2928651 : Nat := 4983230072969 + 3 ^ 40 * 2928651 * 2
def baseEnd_2928651 : Nat := 1503805632270726373193885

theorem tailTrace_2928651 : CollatzResearch.WordTrace tailWord_2928651 prefixEnd_2928651 1503805632270726373193885 := by
  unfold tailWord_2928651
  simp only [CollatzResearch.WordTrace]
  refine ⟨106816677313005075615041807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71211118208670050410027871 106816677313005075615041807)
  ·
    refine ⟨160225015969507613422562711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106816677313005075615041807 160225015969507613422562711)
    ·
      refine ⟨240337523954261420133844067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160225015969507613422562711 240337523954261420133844067)
      ·
        refine ⟨360506285931392130200766101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240337523954261420133844067 360506285931392130200766101)
        ·
          refine ⟨16898732153034006103160911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 360506285931392130200766101 16898732153034006103160911)
          ·
            refine ⟨25348098229551009154741367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16898732153034006103160911 25348098229551009154741367)
            ·
              refine ⟨38022147344326513732112051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25348098229551009154741367 38022147344326513732112051)
              ·
                refine ⟨57033221016489770598168077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38022147344326513732112051 57033221016489770598168077)
                ·
                  refine ⟨21387457881183663974313029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57033221016489770598168077 21387457881183663974313029)
                  ·
                    refine ⟨4010148352721936995183693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21387457881183663974313029 4010148352721936995183693)
                    ·
                      refine ⟨1503805632270726373193885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010148352721936995183693 1503805632270726373193885)
                      ·
                        rfl

theorem cell23_2928651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 3].length) (baseStart_2928651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928651 prefixEnd_2928651 := by exact prefixLift 2928651
  have htrace : WordTrace (prefixWord ++ tailWord_2928651) baseStart_2928651 baseEnd_2928651 := by
    simpa [prefixWord, tailWord_2928651, baseEnd_2928651] using wordTrace_append hprefix tailTrace_2928651
  have hstable : (prefixWord ++ tailWord_2928651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928651).length < 2 ^ (prefixWord ++ tailWord_2928651).sum := by decide
  have hdescent : baseEnd_2928651 < baseStart_2928651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928668 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2928668 : Nat := 118140960795 + 2928668 * 2 ^ 59
def prefixEnd_2928668 : Nat := 4983230072969 + 3 ^ 40 * 2928668 * 2
def baseEnd_2928668 : Nat := 1503814361441852806681307

theorem tailTrace_2928668 : CollatzResearch.WordTrace tailWord_2928668 prefixEnd_2928668 1503814361441852806681307 := by
  unfold tailWord_2928668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53408648676971743759205329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71211531569295658345607105 53408648676971743759205329)
  ·
    refine ⟨40056486507728807819403997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53408648676971743759205329 40056486507728807819403997)
    ·
      refine ⟨15021182440398302932276499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40056486507728807819403997 15021182440398302932276499)
      ·
        refine ⟨22531773660597454398414749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15021182440398302932276499 22531773660597454398414749)
        ·
          refine ⟨8449415122724045399405531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22531773660597454398414749 8449415122724045399405531)
          ·
            refine ⟨12674122684086068099108297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8449415122724045399405531 12674122684086068099108297)
            ·
              refine ⟨9505592013064551074331223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12674122684086068099108297 9505592013064551074331223)
              ·
                refine ⟨14258388019596826611496835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505592013064551074331223 14258388019596826611496835)
                ·
                  refine ⟨21387582029395239917245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14258388019596826611496835 21387582029395239917245253)
                  ·
                    refine ⟨4010171630511607484483485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21387582029395239917245253 4010171630511607484483485)
                    ·
                      refine ⟨1503814361441852806681307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010171630511607484483485 1503814361441852806681307)
                      ·
                        rfl

theorem cell23_2928668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2928668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928668 prefixEnd_2928668 := by exact prefixLift 2928668
  have htrace : WordTrace (prefixWord ++ tailWord_2928668) baseStart_2928668 baseEnd_2928668 := by
    simpa [prefixWord, tailWord_2928668, baseEnd_2928668] using wordTrace_append hprefix tailTrace_2928668
  have hstable : (prefixWord ++ tailWord_2928668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928668).length < 2 ^ (prefixWord ++ tailWord_2928668).sum := by decide
  have hdescent : baseEnd_2928668 < baseStart_2928668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928705 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 6]
def baseStart_2928705 : Nat := 118140960795 + 2928705 * 2 ^ 59
def prefixEnd_2928705 : Nat := 4983230072969 + 3 ^ 40 * 2928705 * 2
def baseEnd_2928705 : Nat := 167092595580674351324293

theorem tailTrace_2928705 : CollatzResearch.WordTrace tailWord_2928705 prefixEnd_2928705 167092595580674351324293 := by
  unfold tailWord_2928705
  simp only [CollatzResearch.WordTrace]
  refine ⟨106818646854809442837507569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71212431236539628558338379 106818646854809442837507569)
  ·
    refine ⟨80113985141107082128130677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106818646854809442837507569 80113985141107082128130677)
    ·
      refine ⟨7510686106978788949512251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80113985141107082128130677 7510686106978788949512251)
      ·
        refine ⟨11266029160468183424268377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7510686106978788949512251 11266029160468183424268377)
        ·
          refine ⟨8449521870351137568201283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11266029160468183424268377 8449521870351137568201283)
          ·
            refine ⟨12674282805526706352301925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8449521870351137568201283 12674282805526706352301925)
            ·
              refine ⟨2376428026036257441056611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12674282805526706352301925 2376428026036257441056611)
              ·
                refine ⟨3564642039054386161584917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376428026036257441056611 3564642039054386161584917)
                ·
                  refine ⟨167092595580674351324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3564642039054386161584917 167092595580674351324293)
                  ·
                    rfl

theorem cell23_2928705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_2928705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928705 prefixEnd_2928705 := by exact prefixLift 2928705
  have htrace : WordTrace (prefixWord ++ tailWord_2928705) baseStart_2928705 baseEnd_2928705 := by
    simpa [prefixWord, tailWord_2928705, baseEnd_2928705] using wordTrace_append hprefix tailTrace_2928705
  have hstable : (prefixWord ++ tailWord_2928705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928705).length < 2 ^ (prefixWord ++ tailWord_2928705).sum := by decide
  have hdescent : baseEnd_2928705 < baseStart_2928705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928718 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2928718 : Nat := 118140960795 + 2928718 * 2 ^ 59
def prefixEnd_2928718 : Nat := 4983230072969 + 3 ^ 40 * 2928718 * 2
def baseEnd_2928718 : Nat := 501280011824859203685359

theorem tailTrace_2928718 : CollatzResearch.WordTrace tailWord_2928718 prefixEnd_2928718 501280011824859203685359 := by
  unfold tailWord_2928718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13352390125470293257216351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71212747335841564038487205 13352390125470293257216351)
  ·
    refine ⟨20028585188205439885824527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13352390125470293257216351 20028585188205439885824527)
    ·
      refine ⟨30042877782308159828736791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20028585188205439885824527 30042877782308159828736791)
      ·
        refine ⟨45064316673462239743105187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30042877782308159828736791 45064316673462239743105187)
        ·
          refine ⟨67596475010193359614657781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45064316673462239743105187 67596475010193359614657781)
          ·
            refine ⟨6337169532205627463874167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67596475010193359614657781 6337169532205627463874167)
            ·
              refine ⟨9505754298308441195811251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337169532205627463874167 9505754298308441195811251)
              ·
                refine ⟨14258631447462661793716877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505754298308441195811251 14258631447462661793716877)
                ·
                  refine ⟨5346986792798498172643829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14258631447462661793716877 5346986792798498172643829)
                  ·
                    refine ⟨501280011824859203685359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5346986792798498172643829 501280011824859203685359)
                    ·
                      rfl

theorem cell23_2928718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2928718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928718 prefixEnd_2928718 := by exact prefixLift 2928718
  have htrace : WordTrace (prefixWord ++ tailWord_2928718) baseStart_2928718 baseEnd_2928718 := by
    simpa [prefixWord, tailWord_2928718, baseEnd_2928718] using wordTrace_append hprefix tailTrace_2928718
  have hstable : (prefixWord ++ tailWord_2928718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928718).length < 2 ^ (prefixWord ++ tailWord_2928718).sum := by decide
  have hdescent : baseEnd_2928718 < baseStart_2928718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928725 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2928725 : Nat := 118140960795 + 2928725 * 2 ^ 59
def prefixEnd_2928725 : Nat := 4983230072969 + 3 ^ 40 * 2928725 * 2
def baseEnd_2928725 : Nat := 1503843629839159083668545

theorem tailTrace_2928725 : CollatzResearch.WordTrace tailWord_2928725 prefixEnd_2928725 1503843629839159083668545 := by
  unfold tailWord_2928725
  simp only [CollatzResearch.WordTrace]
  refine ⟨106819376314736986253235629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71212917543157990835490419 106819376314736986253235629)
  ·
    refine ⟨40057266118026369844963361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106819376314736986253235629 40057266118026369844963361)
    ·
      refine ⟨30042949588519777383722521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40057266118026369844963361 30042949588519777383722521)
      ·
        refine ⟨22532212191389833037791891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30042949588519777383722521 22532212191389833037791891)
        ·
          refine ⟨33798318287084749556687837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22532212191389833037791891 33798318287084749556687837)
          ·
            refine ⟨12674369357656781083757939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33798318287084749556687837 12674369357656781083757939)
            ·
              refine ⟨19011554036485171625636909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12674369357656781083757939 19011554036485171625636909)
              ·
                refine ⟨7129332763681939359613841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19011554036485171625636909 7129332763681939359613841)
                ·
                  refine ⟨5346999572761454519710381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7129332763681939359613841 5346999572761454519710381)
                  ·
                    refine ⟨2005124839785545444891393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5346999572761454519710381 2005124839785545444891393)
                    ·
                      refine ⟨1503843629839159083668545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005124839785545444891393 1503843629839159083668545)
                      ·
                        rfl

theorem cell23_2928725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2928725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928725 prefixEnd_2928725 := by exact prefixLift 2928725
  have htrace : WordTrace (prefixWord ++ tailWord_2928725) baseStart_2928725 baseEnd_2928725 := by
    simpa [prefixWord, tailWord_2928725, baseEnd_2928725] using wordTrace_append hprefix tailTrace_2928725
  have hstable : (prefixWord ++ tailWord_2928725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928725).length < 2 ^ (prefixWord ++ tailWord_2928725).sum := by decide
  have hdescent : baseEnd_2928725 < baseStart_2928725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928765 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_2928765 : Nat := 118140960795 + 2928765 * 2 ^ 59
def prefixEnd_2928765 : Nat := 4983230072969 + 3 ^ 40 * 2928765 * 2
def baseEnd_2928765 : Nat := 501288056355112975722787

theorem tailTrace_2928765 : CollatzResearch.WordTrace tailWord_2928765 prefixEnd_2928765 501288056355112975722787 := by
  unfold tailWord_2928765
  simp only [CollatzResearch.WordTrace]
  refine ⟨106820835234592073084691749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71213890156394715389794499 106820835234592073084691749)
  ·
    refine ⟨20028906606486013703379703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106820835234592073084691749 20028906606486013703379703)
    ·
      refine ⟨30043359909729020555069555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20028906606486013703379703 30043359909729020555069555)
      ·
        refine ⟨45065039864593530832604333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30043359909729020555069555 45065039864593530832604333)
        ·
          refine ⟨16899389949222574062226625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45065039864593530832604333 16899389949222574062226625)
          ·
            refine ⟨12674542461916930546669969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16899389949222574062226625 12674542461916930546669969)
            ·
              refine ⟨9505906846437697910002477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12674542461916930546669969 9505906846437697910002477)
              ·
                refine ⟨3564715067414136716250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9505906846437697910002477 3564715067414136716250929)
                ·
                  refine ⟨2673536300560602537188197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564715067414136716250929 2673536300560602537188197)
                  ·
                    refine ⟨501288056355112975722787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673536300560602537188197 501288056355112975722787)
                    ·
                      rfl

theorem cell23_2928765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_2928765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928765 prefixEnd_2928765 := by exact prefixLift 2928765
  have htrace : WordTrace (prefixWord ++ tailWord_2928765) baseStart_2928765 baseEnd_2928765 := by
    simpa [prefixWord, tailWord_2928765, baseEnd_2928765] using wordTrace_append hprefix tailTrace_2928765
  have hstable : (prefixWord ++ tailWord_2928765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928765).length < 2 ^ (prefixWord ++ tailWord_2928765).sum := by decide
  have hdescent : baseEnd_2928765 < baseStart_2928765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928772 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2928772 : Nat := 118140960795 + 2928772 * 2 ^ 59
def prefixEnd_2928772 : Nat := 4983230072969 + 3 ^ 40 * 2928772 * 2
def baseEnd_2928772 : Nat := 1503867763429920399780829

theorem tailTrace_2928772 : CollatzResearch.WordTrace tailWord_2928772 prefixEnd_2928772 1503867763429920399780829 := by
  unfold tailWord_2928772
  simp only [CollatzResearch.WordTrace]
  refine ⟨53410545272783356640098285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71214060363711142186797713 53410545272783356640098285)
  ·
    refine ⟨20028954477293758740036857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53410545272783356640098285 20028954477293758740036857)
    ·
      refine ⟨15021715857970319055027643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20028954477293758740036857 15021715857970319055027643)
      ·
        refine ⟨22532573786955478582541465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15021715857970319055027643 22532573786955478582541465)
        ·
          refine ⟨16899430340216608936906099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22532573786955478582541465 16899430340216608936906099)
          ·
            refine ⟨25349145510324913405359149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16899430340216608936906099 25349145510324913405359149)
            ·
              refine ⟨9505929566371842527009681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25349145510324913405359149 9505929566371842527009681)
              ·
                refine ⟨7129447174778881895257261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9505929566371842527009681 7129447174778881895257261)
                ·
                  refine ⟨2673542690542080710721473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7129447174778881895257261 2673542690542080710721473)
                  ·
                    refine ⟨2005157017906560533041105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673542690542080710721473 2005157017906560533041105)
                    ·
                      refine ⟨1503867763429920399780829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005157017906560533041105 1503867763429920399780829)
                      ·
                        rfl

theorem cell23_2928772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2928772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928772 prefixEnd_2928772 := by exact prefixLift 2928772
  have htrace : WordTrace (prefixWord ++ tailWord_2928772) baseStart_2928772 baseEnd_2928772 := by
    simpa [prefixWord, tailWord_2928772, baseEnd_2928772] using wordTrace_append hprefix tailTrace_2928772
  have hstable : (prefixWord ++ tailWord_2928772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928772).length < 2 ^ (prefixWord ++ tailWord_2928772).sum := by decide
  have hdescent : baseEnd_2928772 < baseStart_2928772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928789 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_2928789 : Nat := 118140960795 + 2928789 * 2 ^ 59
def prefixEnd_2928789 : Nat := 4983230072969 + 3 ^ 40 * 2928789 * 2
def baseEnd_2928789 : Nat := 1503876492601046833268251

theorem tailTrace_2928789 : CollatzResearch.WordTrace tailWord_2928789 prefixEnd_2928789 1503876492601046833268251 := by
  unfold tailWord_2928789
  simp only [CollatzResearch.WordTrace]
  refine ⟨106821710586505125183565421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71214473724336750122376947 106821710586505125183565421)
  ·
    refine ⟨40058141469939421943837033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106821710586505125183565421 40058141469939421943837033)
    ·
      refine ⟨30043606102454566457877775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40058141469939421943837033 30043606102454566457877775)
      ·
        refine ⟨45065409153681849686816663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30043606102454566457877775 45065409153681849686816663)
        ·
          refine ⟨67598113730522774530224995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45065409153681849686816663 67598113730522774530224995)
          ·
            refine ⟨101397170595784161795337493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67598113730522774530224995 101397170595784161795337493)
            ·
              refine ⟨4752992371677382584156445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101397170595784161795337493 4752992371677382584156445)
              ·
                refine ⟨1782372139379018469058667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4752992371677382584156445 1782372139379018469058667)
                ·
                  refine ⟨2673558209068527703588001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782372139379018469058667 2673558209068527703588001)
                  ·
                    refine ⟨2005168656801395777691001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673558209068527703588001 2005168656801395777691001)
                    ·
                      refine ⟨1503876492601046833268251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005168656801395777691001 1503876492601046833268251)
                      ·
                        rfl

theorem cell23_2928789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_2928789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928789 prefixEnd_2928789 := by exact prefixLift 2928789
  have htrace : WordTrace (prefixWord ++ tailWord_2928789) baseStart_2928789 baseEnd_2928789 := by
    simpa [prefixWord, tailWord_2928789, baseEnd_2928789] using wordTrace_append hprefix tailTrace_2928789
  have hstable : (prefixWord ++ tailWord_2928789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928789).length < 2 ^ (prefixWord ++ tailWord_2928789).sum := by decide
  have hdescent : baseEnd_2928789 < baseStart_2928789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928792 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2928792 : Nat := 118140960795 + 2928792 * 2 ^ 59
def prefixEnd_2928792 : Nat := 4983230072969 + 3 ^ 40 * 2928792 * 2
def baseEnd_2928792 : Nat := 1503878033043010321530737

theorem tailTrace_2928792 : CollatzResearch.WordTrace tailWord_2928792 prefixEnd_2928792 1503878033043010321530737 := by
  unfold tailWord_2928792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53410910002747128347962315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71214546670329504463949753 53410910002747128347962315)
  ·
    refine ⟨80116365004120692521943473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53410910002747128347962315 80116365004120692521943473)
    ·
      refine ⟨60087273753090519391457605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80116365004120692521943473 60087273753090519391457605)
      ·
        refine ⟨11266363828704472385898301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60087273753090519391457605 11266363828704472385898301)
        ·
          refine ⟨4224886435764177144711863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11266363828704472385898301 4224886435764177144711863)
          ·
            refine ⟨6337329653646265717067795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224886435764177144711863 6337329653646265717067795)
            ·
              refine ⟨9505994480469398575601693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337329653646265717067795 9505994480469398575601693)
              ·
                refine ⟨3564747930176024465850635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9505994480469398575601693 3564747930176024465850635)
                ·
                  refine ⟨5347121895264036698775953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564747930176024465850635 5347121895264036698775953)
                  ·
                    refine ⟨4010341421448027524081965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347121895264036698775953 4010341421448027524081965)
                    ·
                      refine ⟨1503878033043010321530737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010341421448027524081965 1503878033043010321530737)
                      ·
                        rfl

theorem cell23_2928792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2928792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928792 prefixEnd_2928792 := by exact prefixLift 2928792
  have htrace : WordTrace (prefixWord ++ tailWord_2928792) baseStart_2928792 baseEnd_2928792 := by
    simpa [prefixWord, tailWord_2928792, baseEnd_2928792] using wordTrace_append hprefix tailTrace_2928792
  have hstable : (prefixWord ++ tailWord_2928792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928792).length < 2 ^ (prefixWord ++ tailWord_2928792).sum := by decide
  have hdescent : baseEnd_2928792 < baseStart_2928792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928805 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2928805 : Nat := 118140960795 + 2928805 * 2 ^ 59
def prefixEnd_2928805 : Nat := 4983230072969 + 3 ^ 40 * 2928805 * 2
def baseEnd_2928805 : Nat := 1503884708291518770668177

theorem tailTrace_2928805 : CollatzResearch.WordTrace tailWord_2928805 prefixEnd_2928805 1503884708291518770668177 := by
  unfold tailWord_2928805
  simp only [CollatzResearch.WordTrace]
  refine ⟨106822294154447159916147869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71214862769631439944098579 106822294154447159916147869)
  ·
    refine ⟨40058360307917684968555451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106822294154447159916147869 40058360307917684968555451)
    ·
      refine ⟨60087540461876527452833177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40058360307917684968555451 60087540461876527452833177)
      ·
        refine ⟨45065655346407395589624883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60087540461876527452833177 45065655346407395589624883)
        ·
          refine ⟨67598483019611093384437325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45065655346407395589624883 67598483019611093384437325)
          ·
            refine ⟨25349431132354160019163997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67598483019611093384437325 25349431132354160019163997)
            ·
              refine ⟨9506036674632810007186499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25349431132354160019163997 9506036674632810007186499)
              ·
                refine ⟨14259055011949215010779749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506036674632810007186499 14259055011949215010779749)
                ·
                  refine ⟨2673572814740477814521203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14259055011949215010779749 2673572814740477814521203)
                  ·
                    refine ⟨4010359222110716721781805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2673572814740477814521203 4010359222110716721781805)
                    ·
                      refine ⟨1503884708291518770668177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010359222110716721781805 1503884708291518770668177)
                      ·
                        rfl

theorem cell23_2928805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2928805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928805 prefixEnd_2928805 := by exact prefixLift 2928805
  have htrace : WordTrace (prefixWord ++ tailWord_2928805) baseStart_2928805 baseEnd_2928805 := by
    simpa [prefixWord, tailWord_2928805, baseEnd_2928805] using wordTrace_append hprefix tailTrace_2928805
  have hstable : (prefixWord ++ tailWord_2928805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928805).length < 2 ^ (prefixWord ++ tailWord_2928805).sum := by decide
  have hdescent : baseEnd_2928805 < baseStart_2928805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928832 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2]
def baseStart_2928832 : Nat := 118140960795 + 2928832 * 2 ^ 59
def prefixEnd_2928832 : Nat := 4983230072969 + 3 ^ 40 * 2928832 * 2
def baseEnd_2928832 : Nat := 1503898572269190165030553

theorem tailTrace_2928832 : CollatzResearch.WordTrace tailWord_2928832 prefixEnd_2928832 1503898572269190165030553 := by
  unfold tailWord_2928832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53411639462674671763690375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71215519283566229018253833 53411639462674671763690375)
  ·
    refine ⟨80117459194012007645535563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53411639462674671763690375 80117459194012007645535563)
    ·
      refine ⟨120176188791018011468303345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80117459194012007645535563 120176188791018011468303345)
      ·
        refine ⟨90132141593263508601227509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120176188791018011468303345 90132141593263508601227509)
        ·
          refine ⟨8449888274368453931365079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90132141593263508601227509 8449888274368453931365079)
          ·
            refine ⟨12674832411552680897047619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8449888274368453931365079 12674832411552680897047619)
            ·
              refine ⟨19012248617329021345571429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12674832411552680897047619 19012248617329021345571429)
              ·
                refine ⟨3564796615749191502294643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19012248617329021345571429 3564796615749191502294643)
                ·
                  refine ⟨5347194923623787253441965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564796615749191502294643 5347194923623787253441965)
                  ·
                    refine ⟨2005198096358920220040737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5347194923623787253441965 2005198096358920220040737)
                    ·
                      refine ⟨1503898572269190165030553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005198096358920220040737 1503898572269190165030553)
                      ·
                        rfl

theorem cell23_2928832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_2928832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928832 prefixEnd_2928832 := by exact prefixLift 2928832
  have htrace : WordTrace (prefixWord ++ tailWord_2928832) baseStart_2928832 baseEnd_2928832 := by
    simpa [prefixWord, tailWord_2928832, baseEnd_2928832] using wordTrace_append hprefix tailTrace_2928832
  have hstable : (prefixWord ++ tailWord_2928832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928832).length < 2 ^ (prefixWord ++ tailWord_2928832).sum := by decide
  have hdescent : baseEnd_2928832 < baseStart_2928832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928858 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2928858 : Nat := 118140960795 + 2928858 * 2 ^ 59
def prefixEnd_2928858 : Nat := 4983230072969 + 3 ^ 40 * 2928858 * 2
def baseEnd_2928858 : Nat := 1503911922766207063305433

theorem tailTrace_2928858 : CollatzResearch.WordTrace tailWord_2928858 prefixEnd_2928858 1503911922766207063305433 := by
  unfold tailWord_2928858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26706056805813787491956807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71216151482170099978551485 26706056805813787491956807)
  ·
    refine ⟨40059085208720681237935211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26706056805813787491956807 40059085208720681237935211)
    ·
      refine ⟨60088627813081021856902817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40059085208720681237935211 60088627813081021856902817)
      ·
        refine ⟨45066470859810766392677113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60088627813081021856902817 45066470859810766392677113)
        ·
          refine ⟨33799853144858074794507835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45066470859810766392677113 33799853144858074794507835)
          ·
            refine ⟨50699779717287112191761753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33799853144858074794507835 50699779717287112191761753)
            ·
              refine ⟨38024834787965334143821315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50699779717287112191761753 38024834787965334143821315)
              ·
                refine ⟨57037252181948001215731973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38024834787965334143821315 57037252181948001215731973)
                ·
                  refine ⟨10694484784115250227949745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57037252181948001215731973 10694484784115250227949745)
                  ·
                    refine ⟨8020863588086437670962309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10694484784115250227949745 8020863588086437670962309)
                    ·
                      refine ⟨1503911922766207063305433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8020863588086437670962309 1503911922766207063305433)
                      ·
                        rfl

theorem cell23_2928858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2928858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928858 prefixEnd_2928858 := by exact prefixLift 2928858
  have htrace : WordTrace (prefixWord ++ tailWord_2928858) baseStart_2928858 baseEnd_2928858 := by
    simpa [prefixWord, tailWord_2928858, baseEnd_2928858] using wordTrace_append hprefix tailTrace_2928858
  have hstable : (prefixWord ++ tailWord_2928858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928858).length < 2 ^ (prefixWord ++ tailWord_2928858).sum := by decide
  have hdescent : baseEnd_2928858 < baseStart_2928858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928879 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 2, 2, 2]
def baseStart_2928879 : Nat := 118140960795 + 2928879 * 2 ^ 59
def prefixEnd_2928879 : Nat := 4983230072969 + 3 ^ 40 * 2928879 * 2
def baseEnd_2928879 : Nat := 1503922705859951481142837

theorem tailTrace_2928879 : CollatzResearch.WordTrace tailWord_2928879 prefixEnd_2928879 1503922705859951481142837 := by
  unfold tailWord_2928879
  simp only [CollatzResearch.WordTrace]
  refine ⟨106824993156179070554341691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71216662104119380369561127 106824993156179070554341691)
  ·
    refine ⟨160237489734268605831512537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106824993156179070554341691 160237489734268605831512537)
    ·
      refine ⟨120178117300701454373634403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160237489734268605831512537 120178117300701454373634403)
      ·
        refine ⟨180267175951052181560451605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120178117300701454373634403 180267175951052181560451605)
        ·
          refine ⟨8450023872705571010646169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180267175951052181560451605 8450023872705571010646169)
          ·
            refine ⟨6337517904529178257984627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450023872705571010646169 6337517904529178257984627)
            ·
              refine ⟨9506276856793767386976941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337517904529178257984627 9506276856793767386976941)
              ·
                refine ⟨3564853821297662770116353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9506276856793767386976941 3564853821297662770116353)
                ·
                  refine ⟨2673640365973247077587265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3564853821297662770116353 2673640365973247077587265)
                  ·
                    refine ⟨2005230274479935308190449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2673640365973247077587265 2005230274479935308190449)
                    ·
                      refine ⟨1503922705859951481142837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005230274479935308190449 1503922705859951481142837)
                      ·
                        rfl

theorem cell23_2928879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 2, 2].length) (baseStart_2928879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928879 prefixEnd_2928879 := by exact prefixLift 2928879
  have htrace : WordTrace (prefixWord ++ tailWord_2928879) baseStart_2928879 baseEnd_2928879 := by
    simpa [prefixWord, tailWord_2928879, baseEnd_2928879] using wordTrace_append hprefix tailTrace_2928879
  have hstable : (prefixWord ++ tailWord_2928879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928879).length < 2 ^ (prefixWord ++ tailWord_2928879).sum := by decide
  have hdescent : baseEnd_2928879 < baseStart_2928879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928908 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2928908 : Nat := 118140960795 + 2928908 * 2 ^ 59
def prefixEnd_2928908 : Nat := 4983230072969 + 3 ^ 40 * 2928908 * 2
def baseEnd_2928908 : Nat := 1503937596798931867680203

theorem tailTrace_2928908 : CollatzResearch.WordTrace tailWord_2928908 prefixEnd_2928908 1503937596798931867680203 := by
  unfold tailWord_2928908
  simp only [CollatzResearch.WordTrace]
  refine ⟨53413025436537004253573689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71217367248716005671431585 53413025436537004253573689)
  ·
    refine ⟨40059769077402753190180267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53413025436537004253573689 40059769077402753190180267)
    ·
      refine ⟨60089653616104129785270401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40059769077402753190180267 60089653616104129785270401)
      ·
        refine ⟨45067240212078097338952801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60089653616104129785270401 45067240212078097338952801)
        ·
          refine ⟨33800430159058573004214601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45067240212078097338952801 33800430159058573004214601)
          ·
            refine ⟨25350322619293929753160951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33800430159058573004214601 25350322619293929753160951)
            ·
              refine ⟨38025483928940894629741427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25350322619293929753160951 38025483928940894629741427)
              ·
                refine ⟨57038225893411341944612141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38025483928940894629741427 57038225893411341944612141)
                ·
                  refine ⟨21389334710029253229229553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57038225893411341944612141 21389334710029253229229553)
                  ·
                    refine ⟨16042001032521939921922165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21389334710029253229229553 16042001032521939921922165)
                    ·
                      refine ⟨1503937596798931867680203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16042001032521939921922165 1503937596798931867680203)
                      ·
                        rfl

theorem cell23_2928908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2928908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928908 prefixEnd_2928908 := by exact prefixLift 2928908
  have htrace : WordTrace (prefixWord ++ tailWord_2928908) baseStart_2928908 baseEnd_2928908 := by
    simpa [prefixWord, tailWord_2928908, baseEnd_2928908] using wordTrace_append hprefix tailTrace_2928908
  have hstable : (prefixWord ++ tailWord_2928908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928908).length < 2 ^ (prefixWord ++ tailWord_2928908).sum := by decide
  have hdescent : baseEnd_2928908 < baseStart_2928908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2928919 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 5]
def baseStart_2928919 : Nat := 118140960795 + 2928919 * 2 ^ 59
def prefixEnd_2928919 : Nat := 4983230072969 + 3 ^ 40 * 2928919 * 2
def baseEnd_2928919 : Nat := 167104805009570147182517

theorem tailTrace_2928919 : CollatzResearch.WordTrace tailWord_2928919 prefixEnd_2928919 167104805009570147182517 := by
  unfold tailWord_2928919
  simp only [CollatzResearch.WordTrace]
  refine ⟨106826452076034157385797811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71217634717356104923865207 106826452076034157385797811)
  ·
    refine ⟨160239678114051236078696717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106826452076034157385797811 160239678114051236078696717)
    ·
      refine ⟨60089879292769213529511269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160239678114051236078696717 60089879292769213529511269)
      ·
        refine ⟨11266852367394227536783363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60089879292769213529511269 11266852367394227536783363)
        ·
          refine ⟨16900278551091341305175045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11266852367394227536783363 16900278551091341305175045)
          ·
            refine ⟨3168802228329626494720321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16900278551091341305175045 3168802228329626494720321)
            ·
              refine ⟨2376601671247219871040241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168802228329626494720321 2376601671247219871040241)
              ·
                refine ⟨1782451253435414903280181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2376601671247219871040241 1782451253435414903280181)
                ·
                  refine ⟨167104805009570147182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782451253435414903280181 167104805009570147182517)
                  ·
                    rfl

theorem cell23_2928919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 5].length) (baseStart_2928919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2928919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2928919 prefixEnd_2928919 := by exact prefixLift 2928919
  have htrace : WordTrace (prefixWord ++ tailWord_2928919) baseStart_2928919 baseEnd_2928919 := by
    simpa [prefixWord, tailWord_2928919, baseEnd_2928919] using wordTrace_append hprefix tailTrace_2928919
  have hstable : (prefixWord ++ tailWord_2928919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2928919).length < 2 ^ (prefixWord ++ tailWord_2928919).sum := by decide
  have hdescent : baseEnd_2928919 < baseStart_2928919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2928919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929045 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2929045 : Nat := 118140960795 + 2929045 * 2 ^ 59
def prefixEnd_2929045 : Nat := 4983230072969 + 3 ^ 40 * 2929045 * 2
def baseEnd_2929045 : Nat := 1504007943648597831667073

theorem tailTrace_2929045 : CollatzResearch.WordTrace tailWord_2929045 prefixEnd_2929045 1504007943648597831667073 := by
  unfold tailWord_2929045
  simp only [CollatzResearch.WordTrace]
  refine ⟨106831047673577680904884589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71220698449051787269923059 106831047673577680904884589)
  ·
    refine ⟨40061642877591630339331721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106831047673577680904884589 40061642877591630339331721)
    ·
      refine ⟨30046232158193722754498791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40061642877591630339331721 30046232158193722754498791)
      ·
        refine ⟨45069348237290584131748187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30046232158193722754498791 45069348237290584131748187)
        ·
          refine ⟨67604022355935876197622281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45069348237290584131748187 67604022355935876197622281)
          ·
            refine ⟨50703016766951907148216711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67604022355935876197622281 50703016766951907148216711)
            ·
              refine ⟨76054525150427860722325067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50703016766951907148216711 76054525150427860722325067)
              ·
                refine ⟨114081787725641791083487601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76054525150427860722325067 114081787725641791083487601)
                ·
                  refine ⟨85561340794231343312615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114081787725641791083487601 85561340794231343312615701)
                  ·
                    refine ⟨4010687849729594217778861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85561340794231343312615701 4010687849729594217778861)
                    ·
                      refine ⟨1504007943648597831667073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010687849729594217778861 1504007943648597831667073)
                      ·
                        rfl

theorem cell23_2929045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2929045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929045 prefixEnd_2929045 := by exact prefixLift 2929045
  have htrace : WordTrace (prefixWord ++ tailWord_2929045) baseStart_2929045 baseEnd_2929045 := by
    simpa [prefixWord, tailWord_2929045, baseEnd_2929045] using wordTrace_append hprefix tailTrace_2929045
  have hstable : (prefixWord ++ tailWord_2929045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929045).length < 2 ^ (prefixWord ++ tailWord_2929045).sum := by decide
  have hdescent : baseEnd_2929045 < baseStart_2929045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929055 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2929055 : Nat := 118140960795 + 2929055 * 2 ^ 59
def prefixEnd_2929055 : Nat := 4983230072969 + 3 ^ 40 * 2929055 * 2
def baseEnd_2929055 : Nat := 1504013078455142792542027

theorem tailTrace_2929055 : CollatzResearch.WordTrace tailWord_2929055 prefixEnd_2929055 1504013078455142792542027 := by
  unfold tailWord_2929055
  simp only [CollatzResearch.WordTrace]
  refine ⟨106831412403541452612748619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71220941602360968408499079 106831412403541452612748619)
  ·
    refine ⟨160247118605312178919122929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106831412403541452612748619 160247118605312178919122929)
    ·
      refine ⟨120185338953984134189342197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160247118605312178919122929 120185338953984134189342197)
      ·
        refine ⟨11267375526936012580250831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120185338953984134189342197 11267375526936012580250831)
        ·
          refine ⟨16901063290404018870376247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11267375526936012580250831 16901063290404018870376247)
          ·
            refine ⟨25351594935606028305564371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901063290404018870376247 25351594935606028305564371)
            ·
              refine ⟨38027392403409042458346557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25351594935606028305564371 38027392403409042458346557)
              ·
                refine ⟨14260272151278390921879959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38027392403409042458346557 14260272151278390921879959)
                ·
                  refine ⟨21390408226917586382819939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14260272151278390921879959 21390408226917586382819939)
                  ·
                    refine ⟨32085612340376379574229909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21390408226917586382819939 32085612340376379574229909)
                    ·
                      refine ⟨1504013078455142792542027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32085612340376379574229909 1504013078455142792542027)
                      ·
                        rfl

theorem cell23_2929055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2929055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929055 prefixEnd_2929055 := by exact prefixLift 2929055
  have htrace : WordTrace (prefixWord ++ tailWord_2929055) baseStart_2929055 baseEnd_2929055 := by
    simpa [prefixWord, tailWord_2929055, baseEnd_2929055] using wordTrace_append hprefix tailTrace_2929055
  have hstable : (prefixWord ++ tailWord_2929055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929055).length < 2 ^ (prefixWord ++ tailWord_2929055).sum := by decide
  have hdescent : baseEnd_2929055 < baseStart_2929055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929059 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 4]
def baseStart_2929059 : Nat := 118140960795 + 2929059 * 2 ^ 59
def prefixEnd_2929059 : Nat := 4983230072969 + 3 ^ 40 * 2929059 * 2
def baseEnd_2929059 : Nat := 1504015132377760776892009

theorem tailTrace_2929059 : CollatzResearch.WordTrace tailWord_2929059 prefixEnd_2929059 1504015132377760776892009 := by
  unfold tailWord_2929059
  simp only [CollatzResearch.WordTrace]
  refine ⟨106831558295526961295894231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71221038863684640863929487 106831558295526961295894231)
  ·
    refine ⟨160247337443290441943841347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106831558295526961295894231 160247337443290441943841347)
    ·
      refine ⟨240371006164935662915762021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160247337443290441943841347 240371006164935662915762021)
      ·
        refine ⟨45069563655925436796705379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240371006164935662915762021 45069563655925436796705379)
        ·
          refine ⟨67604345483888155195058069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45069563655925436796705379 67604345483888155195058069)
          ·
            refine ⟨3168953694557257274768347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67604345483888155195058069 3168953694557257274768347)
            ·
              refine ⟨4753430541835885912152521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168953694557257274768347 4753430541835885912152521)
              ·
                refine ⟨3565072906376914434114391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753430541835885912152521 3565072906376914434114391)
                ·
                  refine ⟨5347609359565371651171587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565072906376914434114391 5347609359565371651171587)
                  ·
                    refine ⟨8021414039348057476757381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5347609359565371651171587 8021414039348057476757381)
                    ·
                      refine ⟨1504015132377760776892009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8021414039348057476757381 1504015132377760776892009)
                      ·
                        rfl

theorem cell23_2929059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_2929059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929059 prefixEnd_2929059 := by exact prefixLift 2929059
  have htrace : WordTrace (prefixWord ++ tailWord_2929059) baseStart_2929059 baseEnd_2929059 := by
    simpa [prefixWord, tailWord_2929059, baseEnd_2929059] using wordTrace_append hprefix tailTrace_2929059
  have hstable : (prefixWord ++ tailWord_2929059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929059).length < 2 ^ (prefixWord ++ tailWord_2929059).sum := by decide
  have hdescent : baseEnd_2929059 < baseStart_2929059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929069 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2929069 : Nat := 118140960795 + 2929069 * 2 ^ 59
def prefixEnd_2929069 : Nat := 4983230072969 + 3 ^ 40 * 2929069 * 2
def baseEnd_2929069 : Nat := 501340089061435245922321

theorem tailTrace_2929069 : CollatzResearch.WordTrace tailWord_2929069 prefixEnd_2929069 501340089061435245922321 := by
  unfold tailWord_2929069
  simp only [CollatzResearch.WordTrace]
  refine ⟨106831923025490733003758261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71221282016993822002505507 106831923025490733003758261)
  ·
    refine ⟨10015492783639756219102337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106831923025490733003758261 10015492783639756219102337)
    ·
      refine ⟨7511619587729817164326753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10015492783639756219102337 7511619587729817164326753)
      ·
        refine ⟨5633714690797362873245065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7511619587729817164326753 5633714690797362873245065)
        ·
          refine ⟨4225286018098022154933799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5633714690797362873245065 4225286018098022154933799)
          ·
            refine ⟨6337929027147033232400699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225286018098022154933799 6337929027147033232400699)
            ·
              refine ⟨9506893540720549848601049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337929027147033232400699 9506893540720549848601049)
              ·
                refine ⟨7130170155540412386450787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9506893540720549848601049 7130170155540412386450787)
                ·
                  refine ⟨10695255233310618579676181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130170155540412386450787 10695255233310618579676181)
                  ·
                    refine ⟨501340089061435245922321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10695255233310618579676181 501340089061435245922321)
                    ·
                      rfl

theorem cell23_2929069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2929069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929069 prefixEnd_2929069 := by exact prefixLift 2929069
  have htrace : WordTrace (prefixWord ++ tailWord_2929069) baseStart_2929069 baseEnd_2929069 := by
    simpa [prefixWord, tailWord_2929069, baseEnd_2929069] using wordTrace_append hprefix tailTrace_2929069
  have hstable : (prefixWord ++ tailWord_2929069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929069).length < 2 ^ (prefixWord ++ tailWord_2929069).sum := by decide
  have hdescent : baseEnd_2929069 < baseStart_2929069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929095 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 7]
def baseStart_2929095 : Nat := 118140960795 + 2929095 * 2 ^ 59
def prefixEnd_2929095 : Nat := 4983230072969 + 3 ^ 40 * 2929095 * 2
def baseEnd_2929095 : Nat := 501344539227107545347281

theorem tailTrace_2929095 : CollatzResearch.WordTrace tailWord_2929095 prefixEnd_2929095 501344539227107545347281 := by
  unfold tailWord_2929095
  simp only [CollatzResearch.WordTrace]
  refine ⟨106832871323396539444204739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71221914215597692962803159 106832871323396539444204739)
  ·
    refine ⟨160249306985094809166307109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106832871323396539444204739 160249306985094809166307109)
    ·
      refine ⟨30046745059705276718682583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160249306985094809166307109 30046745059705276718682583)
      ·
        refine ⟨45070117589557915078023875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30046745059705276718682583 45070117589557915078023875)
        ·
          refine ⟨67605176384336872617035813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45070117589557915078023875 67605176384336872617035813)
          ·
            refine ⟨12675970572063163615694215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67605176384336872617035813 12675970572063163615694215)
            ·
              refine ⟨19013955858094745423541323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12675970572063163615694215 19013955858094745423541323)
              ·
                refine ⟨28520933787142118135311985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013955858094745423541323 28520933787142118135311985)
                ·
                  refine ⟨21390700340356588601483989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28520933787142118135311985 21390700340356588601483989)
                  ·
                    refine ⟨501344539227107545347281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21390700340356588601483989 501344539227107545347281)
                    ·
                      rfl

theorem cell23_2929095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_2929095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929095 prefixEnd_2929095 := by exact prefixLift 2929095
  have htrace : WordTrace (prefixWord ++ tailWord_2929095) baseStart_2929095 baseEnd_2929095 := by
    simpa [prefixWord, tailWord_2929095, baseEnd_2929095] using wordTrace_append hprefix tailTrace_2929095
  have hstable : (prefixWord ++ tailWord_2929095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929095).length < 2 ^ (prefixWord ++ tailWord_2929095).sum := by decide
  have hdescent : baseEnd_2929095 < baseStart_2929095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929106 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2929106 : Nat := 118140960795 + 2929106 * 2 ^ 59
def prefixEnd_2929106 : Nat := 4983230072969 + 3 ^ 40 * 2929106 * 2
def baseEnd_2929106 : Nat := 1504039265968522093004293

theorem tailTrace_2929106 : CollatzResearch.WordTrace tailWord_2929106 prefixEnd_2929106 1504039265968522093004293 := by
  unfold tailWord_2929106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708318131589172080713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71222181684237792215236781 26708318131589172080713793)
  ·
    refine ⟨20031238598691879060535345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26708318131589172080713793 20031238598691879060535345)
    ·
      refine ⟨15023428949018909295401509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20031238598691879060535345 15023428949018909295401509)
      ·
        refine ⟨2816892927941045492887783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15023428949018909295401509 2816892927941045492887783)
        ·
          refine ⟨4225339391911568239331675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816892927941045492887783 4225339391911568239331675)
          ·
            refine ⟨6338009087867352358997513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225339391911568239331675 6338009087867352358997513)
            ·
              refine ⟨4753506815900514269248135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338009087867352358997513 4753506815900514269248135)
              ·
                refine ⟨7130260223850771403872203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753506815900514269248135 7130260223850771403872203)
                ·
                  refine ⟨10695390335776157105808305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130260223850771403872203 10695390335776157105808305)
                  ·
                    refine ⟨8021542751832117829356229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10695390335776157105808305 8021542751832117829356229)
                    ·
                      refine ⟨1504039265968522093004293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8021542751832117829356229 1504039265968522093004293)
                      ·
                        rfl

theorem cell23_2929106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2929106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929106 prefixEnd_2929106 := by exact prefixLift 2929106
  have htrace : WordTrace (prefixWord ++ tailWord_2929106) baseStart_2929106 baseEnd_2929106 := by
    simpa [prefixWord, tailWord_2929106, baseEnd_2929106] using wordTrace_append hprefix tailTrace_2929106
  have hstable : (prefixWord ++ tailWord_2929106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929106).length < 2 ^ (prefixWord ++ tailWord_2929106).sum := by decide
  have hdescent : baseEnd_2929106 < baseStart_2929106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929109 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2929109 : Nat := 118140960795 + 2929109 * 2 ^ 59
def prefixEnd_2929109 : Nat := 4983230072969 + 3 ^ 40 * 2929109 * 2
def baseEnd_2929109 : Nat := 1504040806410485581266779

theorem tailTrace_2929109 : CollatzResearch.WordTrace tailWord_2929109 prefixEnd_2929109 1504040806410485581266779 := by
  unfold tailWord_2929109
  simp only [CollatzResearch.WordTrace]
  refine ⟨106833381945345819835214381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71222254630230546556809587 106833381945345819835214381)
  ·
    refine ⟨40062518229504682438205393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106833381945345819835214381 40062518229504682438205393)
    ·
      refine ⟨30046888672128511828654045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40062518229504682438205393 30046888672128511828654045)
      ·
        refine ⟨11267583252048191935745267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30046888672128511828654045 11267583252048191935745267)
        ·
          refine ⟨16901374878072287903617901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11267583252048191935745267 16901374878072287903617901)
          ·
            refine ⟨6338015579277107963856713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16901374878072287903617901 6338015579277107963856713)
            ·
              refine ⟨4753511684457830972892535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338015579277107963856713 4753511684457830972892535)
              ·
                refine ⟨7130267526686746459338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753511684457830972892535 7130267526686746459338803)
                ·
                  refine ⟨10695401290030119689008205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130267526686746459338803 10695401290030119689008205)
                  ·
                    refine ⟨4010775483761294883378077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10695401290030119689008205 4010775483761294883378077)
                    ·
                      refine ⟨1504040806410485581266779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4010775483761294883378077 1504040806410485581266779)
                      ·
                        rfl

theorem cell23_2929109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2929109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929109 prefixEnd_2929109 := by exact prefixLift 2929109
  have htrace : WordTrace (prefixWord ++ tailWord_2929109) baseStart_2929109 baseEnd_2929109 := by
    simpa [prefixWord, tailWord_2929109, baseEnd_2929109] using wordTrace_append hprefix tailTrace_2929109
  have hstable : (prefixWord ++ tailWord_2929109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929109).length < 2 ^ (prefixWord ++ tailWord_2929109).sum := by decide
  have hdescent : baseEnd_2929109 < baseStart_2929109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929119 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 3, 3, 2]
def baseStart_2929119 : Nat := 118140960795 + 2929119 * 2 ^ 59
def prefixEnd_2929119 : Nat := 4983230072969 + 3 ^ 40 * 2929119 * 2
def baseEnd_2929119 : Nat := 1504045941217030542141733

theorem tailTrace_2929119 : CollatzResearch.WordTrace tailWord_2929119 prefixEnd_2929119 1504045941217030542141733 := by
  unfold tailWord_2929119
  simp only [CollatzResearch.WordTrace]
  refine ⟨106833746675309591543078411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71222497783539727695385607 106833746675309591543078411)
  ·
    refine ⟨160250620012964387314617617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106833746675309591543078411 160250620012964387314617617)
    ·
      refine ⟨120187965009723290485963213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160250620012964387314617617 120187965009723290485963213)
      ·
        refine ⟨45070486878646233932236205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120187965009723290485963213 45070486878646233932236205)
        ·
          refine ⟨16901432579492337724588577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45070486878646233932236205 16901432579492337724588577)
          ·
            refine ⟨12676074434619253293441433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16901432579492337724588577 12676074434619253293441433)
            ·
              refine ⟨9507055825964439970081075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12676074434619253293441433 9507055825964439970081075)
              ·
                refine ⟨14260583738946659955121613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9507055825964439970081075 14260583738946659955121613)
                ·
                  refine ⟨5347718902104997483170605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14260583738946659955121613 5347718902104997483170605)
                  ·
                    refine ⟨2005394588289374056188977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5347718902104997483170605 2005394588289374056188977)
                    ·
                      refine ⟨1504045941217030542141733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005394588289374056188977 1504045941217030542141733)
                      ·
                        rfl

theorem cell23_2929119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_2929119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929119 prefixEnd_2929119 := by exact prefixLift 2929119
  have htrace : WordTrace (prefixWord ++ tailWord_2929119) baseStart_2929119 baseEnd_2929119 := by
    simpa [prefixWord, tailWord_2929119, baseEnd_2929119] using wordTrace_append hprefix tailTrace_2929119
  have hstable : (prefixWord ++ tailWord_2929119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929119).length < 2 ^ (prefixWord ++ tailWord_2929119).sum := by decide
  have hdescent : baseEnd_2929119 < baseStart_2929119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929135 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_2929135 : Nat := 118140960795 + 2929135 * 2 ^ 59
def prefixEnd_2929135 : Nat := 4983230072969 + 3 ^ 40 * 2929135 * 2
def baseEnd_2929135 : Nat := 1504054156907502479541659

theorem tailTrace_2929135 : CollatzResearch.WordTrace tailWord_2929135 prefixEnd_2929135 1504054156907502479541659 := by
  unfold tailWord_2929135
  simp only [CollatzResearch.WordTrace]
  refine ⟨106834330243251626275660859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71222886828834417517107239 106834330243251626275660859)
  ·
    refine ⟨160251495364877439413491289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106834330243251626275660859 160251495364877439413491289)
    ·
      refine ⟨120188621523658079560118467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160251495364877439413491289 120188621523658079560118467)
      ·
        refine ⟨180282932285487119340177701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120188621523658079560118467 180282932285487119340177701)
        ·
          refine ⟨33803049803528834876283319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180282932285487119340177701 33803049803528834876283319)
          ·
            refine ⟨50704574705293252314424979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803049803528834876283319 50704574705293252314424979)
            ·
              refine ⟨76056862057939878471637469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50704574705293252314424979 76056862057939878471637469)
              ·
                refine ⟨28521323271727454426864051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76056862057939878471637469 28521323271727454426864051)
                ·
                  refine ⟨42781984907591181640296077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28521323271727454426864051 42781984907591181640296077)
                  ·
                    refine ⟨16043244340346693115111029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42781984907591181640296077 16043244340346693115111029)
                    ·
                      refine ⟨1504054156907502479541659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16043244340346693115111029 1504054156907502479541659)
                      ·
                        rfl

theorem cell23_2929135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_2929135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929135 prefixEnd_2929135 := by exact prefixLift 2929135
  have htrace : WordTrace (prefixWord ++ tailWord_2929135) baseStart_2929135 baseEnd_2929135 := by
    simpa [prefixWord, tailWord_2929135, baseEnd_2929135] using wordTrace_append hprefix tailTrace_2929135
  have hstable : (prefixWord ++ tailWord_2929135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929135).length < 2 ^ (prefixWord ++ tailWord_2929135).sum := by decide
  have hdescent : baseEnd_2929135 < baseStart_2929135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929142 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2929142 : Nat := 118140960795 + 2929142 * 2 ^ 59
def prefixEnd_2929142 : Nat := 4983230072969 + 3 ^ 40 * 2929142 * 2
def baseEnd_2929142 : Nat := 501352583757361317384709

theorem tailTrace_2929142 : CollatzResearch.WordTrace tailWord_2929142 prefixEnd_2929142 501352583757361317384709 := by
  unfold tailWord_2929142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677161597139141654447855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71223057036150844314110453 6677161597139141654447855)
  ·
    refine ⟨10015742395708712481671783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6677161597139141654447855 10015742395708712481671783)
    ·
      refine ⟨15023613593563068722507675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10015742395708712481671783 15023613593563068722507675)
      ·
        refine ⟨22535420390344603083761513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15023613593563068722507675 22535420390344603083761513)
        ·
          refine ⟨16901565292758452312821135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22535420390344603083761513 16901565292758452312821135)
          ·
            refine ⟨25352347939137678469231703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901565292758452312821135 25352347939137678469231703)
            ·
              refine ⟨38028521908706517703847555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25352347939137678469231703 38028521908706517703847555)
              ·
                refine ⟨57042782863059776555771333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38028521908706517703847555 57042782863059776555771333)
                ·
                  refine ⟨10695521786823708104207125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57042782863059776555771333 10695521786823708104207125)
                  ·
                    refine ⟨501352583757361317384709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10695521786823708104207125 501352583757361317384709)
                    ·
                      rfl

theorem cell23_2929142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2929142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929142 prefixEnd_2929142 := by exact prefixLift 2929142
  have htrace : WordTrace (prefixWord ++ tailWord_2929142) baseStart_2929142 baseEnd_2929142 := by
    simpa [prefixWord, tailWord_2929142, baseEnd_2929142] using wordTrace_append hprefix tailTrace_2929142
  have hstable : (prefixWord ++ tailWord_2929142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929142).length < 2 ^ (prefixWord ++ tailWord_2929142).sum := by decide
  have hdescent : baseEnd_2929142 < baseStart_2929142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929162 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_2929162 : Nat := 118140960795 + 2929162 * 2 ^ 59
def prefixEnd_2929162 : Nat := 4983230072969 + 3 ^ 40 * 2929162 * 2
def baseEnd_2929162 : Nat := 1504068020885173873904035

theorem tailTrace_2929162 : CollatzResearch.WordTrace tailWord_2929162 prefixEnd_2929162 1504068020885173873904035 := by
  unfold tailWord_2929162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26708828753538452471723435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71223543342769206591262493 26708828753538452471723435)
  ·
    refine ⟨40063243130307678707585153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26708828753538452471723435 40063243130307678707585153)
    ·
      refine ⟨30047432347730759030688865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063243130307678707585153 30047432347730759030688865)
      ·
        refine ⟨22535574260798069273016649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047432347730759030688865 22535574260798069273016649)
        ·
          refine ⟨16901680695598551954762487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22535574260798069273016649 16901680695598551954762487)
          ·
            refine ⟨25352521043397827932143731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901680695598551954762487 25352521043397827932143731)
            ·
              refine ⟨38028781565096741898215597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25352521043397827932143731 38028781565096741898215597)
              ·
                refine ⟨14260793086911278211830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38028781565096741898215597 14260793086911278211830849)
                ·
                  refine ⟨10695594815183458658873137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14260793086911278211830849 10695594815183458658873137)
                  ·
                    refine ⟨8021696111387593994154853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10695594815183458658873137 8021696111387593994154853)
                    ·
                      refine ⟨1504068020885173873904035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8021696111387593994154853 1504068020885173873904035)
                      ·
                        rfl

theorem cell23_2929162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_2929162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929162 prefixEnd_2929162 := by exact prefixLift 2929162
  have htrace : WordTrace (prefixWord ++ tailWord_2929162) baseStart_2929162 baseEnd_2929162 := by
    simpa [prefixWord, tailWord_2929162, baseEnd_2929162] using wordTrace_append hprefix tailTrace_2929162
  have hstable : (prefixWord ++ tailWord_2929162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929162).length < 2 ^ (prefixWord ++ tailWord_2929162).sum := by decide
  have hdescent : baseEnd_2929162 < baseStart_2929162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929166 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2929166 : Nat := 118140960795 + 2929166 * 2 ^ 59
def prefixEnd_2929166 : Nat := 4983230072969 + 3 ^ 40 * 2929166 * 2
def baseEnd_2929166 : Nat := 1504070074807791858254017

theorem tailTrace_2929166 : CollatzResearch.WordTrace tailWord_2929166 prefixEnd_2929166 1504070074807791858254017 := by
  unfold tailWord_2929166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13354432613267414821254919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71223640604092879046692901 13354432613267414821254919)
  ·
    refine ⟨20031648919901122231882379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13354432613267414821254919 20031648919901122231882379)
    ·
      refine ⟨30047473379851683347823569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20031648919901122231882379 30047473379851683347823569)
      ·
        refine ⟨22535605034888762510867677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047473379851683347823569 22535605034888762510867677)
        ·
          refine ⟨8450851888083285941575379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22535605034888762510867677 8450851888083285941575379)
          ·
            refine ⟨12676277832124928912363069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8450851888083285941575379 12676277832124928912363069)
            ·
              refine ⟨4753604187046848342136151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12676277832124928912363069 4753604187046848342136151)
              ·
                refine ⟨7130406280570272513204227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753604187046848342136151 7130406280570272513204227)
                ·
                  refine ⟨10695609420855408769806341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130406280570272513204227 10695609420855408769806341)
                  ·
                    refine ⟨2005426766410389144338689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10695609420855408769806341 2005426766410389144338689)
                    ·
                      refine ⟨1504070074807791858254017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005426766410389144338689 1504070074807791858254017)
                      ·
                        rfl

theorem cell23_2929166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2929166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929166 prefixEnd_2929166 := by exact prefixLift 2929166
  have htrace : WordTrace (prefixWord ++ tailWord_2929166) baseStart_2929166 baseEnd_2929166 := by
    simpa [prefixWord, tailWord_2929166, baseEnd_2929166] using wordTrace_append hprefix tailTrace_2929166
  have hstable : (prefixWord ++ tailWord_2929166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929166).length < 2 ^ (prefixWord ++ tailWord_2929166).sum := by decide
  have hdescent : baseEnd_2929166 < baseStart_2929166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929189 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 5]
def baseStart_2929189 : Nat := 118140960795 + 2929189 * 2 ^ 59
def prefixEnd_2929189 : Nat := 4983230072969 + 3 ^ 40 * 2929189 * 2
def baseEnd_2929189 : Nat := 167120209429205029807379

theorem tailTrace_2929189 : CollatzResearch.WordTrace tailWord_2929189 prefixEnd_2929189 167120209429205029807379 := by
  unfold tailWord_2929189
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836299785055993498126621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71224199856703995665417747 106836299785055993498126621)
  ·
    refine ⟨40063612419395997561797483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106836299785055993498126621 40063612419395997561797483)
    ·
      refine ⟨60095418629093996342696225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40063612419395997561797483 60095418629093996342696225)
      ·
        refine ⟨45071563971820497257022169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60095418629093996342696225 45071563971820497257022169)
        ·
          refine ⟨33803672978865372942766627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45071563971820497257022169 33803672978865372942766627)
          ·
            refine ⟨50705509468298059414149941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803672978865372942766627 50705509468298059414149941)
            ·
              refine ⟨4753641512652943070076557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50705509468298059414149941 4753641512652943070076557)
              ·
                refine ⟨1782615567244853651278709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753641512652943070076557 1782615567244853651278709)
                ·
                  refine ⟨167120209429205029807379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1782615567244853651278709 167120209429205029807379)
                  ·
                    rfl

theorem cell23_2929189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_2929189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929189 prefixEnd_2929189 := by exact prefixLift 2929189
  have htrace : WordTrace (prefixWord ++ tailWord_2929189) baseStart_2929189 baseEnd_2929189 := by
    simpa [prefixWord, tailWord_2929189, baseEnd_2929189] using wordTrace_append hprefix tailTrace_2929189
  have hstable : (prefixWord ++ tailWord_2929189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929189).length < 2 ^ (prefixWord ++ tailWord_2929189).sum := by decide
  have hdescent : baseEnd_2929189 < baseStart_2929189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929195 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_2929195 : Nat := 118140960795 + 2929195 * 2 ^ 59
def prefixEnd_2929195 : Nat := 4983230072969 + 3 ^ 40 * 2929195 * 2
def baseEnd_2929195 : Nat := 1504084965746772244791383

theorem tailTrace_2929195 : CollatzResearch.WordTrace tailWord_2929195 prefixEnd_2929195 1504084965746772244791383 := by
  unfold tailWord_2929195
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836518623034256522845039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71224345748689504348563359 106836518623034256522845039)
  ·
    refine ⟨160254777934551384784267559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106836518623034256522845039 160254777934551384784267559)
    ·
      refine ⟨240382166901827077176401339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160254777934551384784267559 240382166901827077176401339)
      ·
        refine ⟨360573250352740615764602009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240382166901827077176401339 360573250352740615764602009)
        ·
          refine ⟨270429937764555461823451507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360573250352740615764602009 270429937764555461823451507)
          ·
            refine ⟨405644906646833192735177261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270429937764555461823451507 405644906646833192735177261)
            ·
              refine ⟨152116839992562447275691473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405644906646833192735177261 152116839992562447275691473)
              ·
                refine ⟨114087629994421835456768605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152116839992562447275691473 114087629994421835456768605)
                ·
                  refine ⟨42782861247908188296288227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114087629994421835456768605 42782861247908188296288227)
                  ·
                    refine ⟨64174291871862282444432341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42782861247908188296288227 64174291871862282444432341)
                    ·
                      refine ⟨1504084965746772244791383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64174291871862282444432341 1504084965746772244791383)
                      ·
                        rfl

theorem cell23_2929195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_2929195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929195 prefixEnd_2929195 := by exact prefixLift 2929195
  have htrace : WordTrace (prefixWord ++ tailWord_2929195) baseStart_2929195 baseEnd_2929195 := by
    simpa [prefixWord, tailWord_2929195, baseEnd_2929195] using wordTrace_append hprefix tailTrace_2929195
  have hstable : (prefixWord ++ tailWord_2929195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929195).length < 2 ^ (prefixWord ++ tailWord_2929195).sum := by decide
  have hdescent : baseEnd_2929195 < baseStart_2929195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929202 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_2929202 : Nat := 118140960795 + 2929202 * 2 ^ 59
def prefixEnd_2929202 : Nat := 4983230072969 + 3 ^ 40 * 2929202 * 2
def baseEnd_2929202 : Nat := 501362853370451239134617

theorem tailTrace_2929202 : CollatzResearch.WordTrace tailWord_2929202 prefixEnd_2929202 501362853370451239134617 := by
  unfold tailWord_2929202
  simp only [CollatzResearch.WordTrace]
  refine ⟨26709193483502224179587465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71224515956005931145566573 26709193483502224179587465)
  ·
    refine ⟨20031895112626668134690599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26709193483502224179587465 20031895112626668134690599)
    ·
      refine ⟨30047842668940002202035899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20031895112626668134690599 30047842668940002202035899)
      ·
        refine ⟨45071764003410003303053849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30047842668940002202035899 45071764003410003303053849)
        ·
          refine ⟨33803823002557502477290387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45071764003410003303053849 33803823002557502477290387)
          ·
            refine ⟨50705734503836253715935581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803823002557502477290387 50705734503836253715935581)
            ·
              refine ⟨19014650438938595143475843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50705734503836253715935581 19014650438938595143475843)
              ·
                refine ⟨28521975658407892715213765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19014650438938595143475843 28521975658407892715213765)
                ·
                  refine ⟨5347870435951479884102581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28521975658407892715213765 5347870435951479884102581)
                  ·
                    refine ⟨501362853370451239134617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5347870435951479884102581 501362853370451239134617)
                    ·
                      rfl

theorem cell23_2929202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_2929202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929202 prefixEnd_2929202 := by exact prefixLift 2929202
  have htrace : WordTrace (prefixWord ++ tailWord_2929202) baseStart_2929202 baseEnd_2929202 := by
    simpa [prefixWord, tailWord_2929202, baseEnd_2929202] using wordTrace_append hprefix tailTrace_2929202
  have hstable : (prefixWord ++ tailWord_2929202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929202).length < 2 ^ (prefixWord ++ tailWord_2929202).sum := by decide
  have hdescent : baseEnd_2929202 < baseStart_2929202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929206 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2929206 : Nat := 118140960795 + 2929206 * 2 ^ 59
def prefixEnd_2929206 : Nat := 4983230072969 + 3 ^ 40 * 2929206 * 2
def baseEnd_2929206 : Nat := 167121179337107966861537

theorem tailTrace_2929206 : CollatzResearch.WordTrace tailWord_2929206 prefixEnd_2929206 167121179337107966861537 := by
  unfold tailWord_2929206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6677307489124650337593467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71224613217329603600996981 6677307489124650337593467)
  ·
    refine ⟨10015961233686975506390201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6677307489124650337593467 10015961233686975506390201)
    ·
      refine ⟨7511970925265231629792651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10015961233686975506390201 7511970925265231629792651)
      ·
        refine ⟨11267956387897847444688977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7511970925265231629792651 11267956387897847444688977)
        ·
          refine ⟨8450967290923385583516733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11267956387897847444688977 8450967290923385583516733)
          ·
            refine ⟨3169112734096269593818775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8450967290923385583516733 3169112734096269593818775)
            ·
              refine ⟨4753669101144404390728163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3169112734096269593818775 4753669101144404390728163)
              ·
                refine ⟨7130503651716606586092245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753669101144404390728163 7130503651716606586092245)
                ·
                  refine ⟨167121179337107966861537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7130503651716606586092245 167121179337107966861537)
                  ·
                    rfl

theorem cell23_2929206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2929206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929206 prefixEnd_2929206 := by exact prefixLift 2929206
  have htrace : WordTrace (prefixWord ++ tailWord_2929206) baseStart_2929206 baseEnd_2929206 := by
    simpa [prefixWord, tailWord_2929206, baseEnd_2929206] using wordTrace_append hprefix tailTrace_2929206
  have hstable : (prefixWord ++ tailWord_2929206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929206).length < 2 ^ (prefixWord ++ tailWord_2929206).sum := by decide
  have hdescent : baseEnd_2929206 < baseStart_2929206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929209 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2929209 : Nat := 118140960795 + 2929209 * 2 ^ 59
def prefixEnd_2929209 : Nat := 4983230072969 + 3 ^ 40 * 2929209 * 2
def baseEnd_2929209 : Nat := 1504092154475935190016319

theorem tailTrace_2929209 : CollatzResearch.WordTrace tailWord_2929209 prefixEnd_2929209 1504092154475935190016319 := by
  unfold tailWord_2929209
  simp only [CollatzResearch.WordTrace]
  refine ⟨106837029244983536913854681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71224686163322357942569787 106837029244983536913854681)
  ·
    refine ⟨80127771933737652685391011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106837029244983536913854681 80127771933737652685391011)
    ·
      refine ⟨120191657900606479028086517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80127771933737652685391011 120191657900606479028086517)
      ·
        refine ⟨11267967928181857408883111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120191657900606479028086517 11267967928181857408883111)
        ·
          refine ⟨16901951892272786113324667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11267967928181857408883111 16901951892272786113324667)
          ·
            refine ⟨25352927838409179169987001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901951892272786113324667 25352927838409179169987001)
            ·
              refine ⟨19014695878806884377490251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25352927838409179169987001 19014695878806884377490251)
              ·
                refine ⟨28522043818210326566235377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19014695878806884377490251 28522043818210326566235377)
                ·
                  refine ⟨21391532863657744924676533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28522043818210326566235377 21391532863657744924676533)
                  ·
                    refine ⟨2005456205967913586688425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21391532863657744924676533 2005456205967913586688425)
                    ·
                      refine ⟨1504092154475935190016319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005456205967913586688425 1504092154475935190016319)
                      ·
                        rfl

theorem cell23_2929209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2929209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929209 prefixEnd_2929209 := by exact prefixLift 2929209
  have htrace : WordTrace (prefixWord ++ tailWord_2929209) baseStart_2929209 baseEnd_2929209 := by
    simpa [prefixWord, tailWord_2929209, baseEnd_2929209] using wordTrace_append hprefix tailTrace_2929209
  have hstable : (prefixWord ++ tailWord_2929209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929209).length < 2 ^ (prefixWord ++ tailWord_2929209).sum := by decide
  have hdescent : baseEnd_2929209 < baseStart_2929209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929212 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2929212 : Nat := 118140960795 + 2929212 * 2 ^ 59
def prefixEnd_2929212 : Nat := 4983230072969 + 3 ^ 40 * 2929212 * 2
def baseEnd_2929212 : Nat := 1504093694917898678278805

theorem tailTrace_2929212 : CollatzResearch.WordTrace tailWord_2929212 prefixEnd_2929212 1504093694917898678278805 := by
  unfold tailWord_2929212
  simp only [CollatzResearch.WordTrace]
  refine ⟨53418569331986334213106945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71224759109315112284142593 53418569331986334213106945)
  ·
    refine ⟨40063926998989750659830209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53418569331986334213106945 40063926998989750659830209)
    ·
      refine ⟨30047945249242312994872657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40063926998989750659830209 30047945249242312994872657)
      ·
        refine ⟨22535958936931734746154493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047945249242312994872657 22535958936931734746154493)
        ·
          refine ⟨8450984601349400529807935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22535958936931734746154493 8450984601349400529807935)
          ·
            refine ⟨12676476902024100794711903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8450984601349400529807935 12676476902024100794711903)
            ·
              refine ⟨19014715353036151192067855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12676476902024100794711903 19014715353036151192067855)
              ·
                refine ⟨28522073029554226788101783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19014715353036151192067855 28522073029554226788101783)
                ·
                  refine ⟨42783109544331340182152675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28522073029554226788101783 42783109544331340182152675)
                  ·
                    refine ⟨64174664316497010273229013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42783109544331340182152675 64174664316497010273229013)
                    ·
                      refine ⟨1504093694917898678278805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64174664316497010273229013 1504093694917898678278805)
                      ·
                        rfl

theorem cell23_2929212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2929212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929212 prefixEnd_2929212 := by exact prefixLift 2929212
  have htrace : WordTrace (prefixWord ++ tailWord_2929212) baseStart_2929212 baseEnd_2929212 := by
    simpa [prefixWord, tailWord_2929212, baseEnd_2929212] using wordTrace_append hprefix tailTrace_2929212
  have hstable : (prefixWord ++ tailWord_2929212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929212).length < 2 ^ (prefixWord ++ tailWord_2929212).sum := by decide
  have hdescent : baseEnd_2929212 < baseStart_2929212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929239 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_2929239 : Nat := 118140960795 + 2929239 * 2 ^ 59
def prefixEnd_2929239 : Nat := 4983230072969 + 3 ^ 40 * 2929239 * 2
def baseEnd_2929239 : Nat := 1504107558895570072641181

theorem tailTrace_2929239 : CollatzResearch.WordTrace tailWord_2929239 prefixEnd_2929239 1504107558895570072641181 := by
  unfold tailWord_2929239
  simp only [CollatzResearch.WordTrace]
  refine ⟨106838123434874852037446771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71225415623249901358297847 106838123434874852037446771)
  ·
    refine ⟨160257185152312278056170157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106838123434874852037446771 160257185152312278056170157)
    ·
      refine ⟨60096444432117104271063809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160257185152312278056170157 60096444432117104271063809)
      ·
        refine ⟨45072333324087828203297857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60096444432117104271063809 45072333324087828203297857)
        ·
          refine ⟨33804249993065871152473393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45072333324087828203297857 33804249993065871152473393)
          ·
            refine ⟨25353187494799403364355045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33804249993065871152473393 25353187494799403364355045)
            ·
              refine ⟨4753722655274888130816571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25353187494799403364355045 4753722655274888130816571)
              ·
                refine ⟨7130583982912332196224857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753722655274888130816571 7130583982912332196224857)
                ·
                  refine ⟨5347937987184249147168643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7130583982912332196224857 5347937987184249147168643)
                  ·
                    refine ⟨8021906980776373720752965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5347937987184249147168643 8021906980776373720752965)
                    ·
                      refine ⟨1504107558895570072641181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8021906980776373720752965 1504107558895570072641181)
                      ·
                        rfl

theorem cell23_2929239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_2929239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929239 prefixEnd_2929239 := by exact prefixLift 2929239
  have htrace : WordTrace (prefixWord ++ tailWord_2929239) baseStart_2929239 baseEnd_2929239 := by
    simpa [prefixWord, tailWord_2929239, baseEnd_2929239] using wordTrace_append hprefix tailTrace_2929239
  have hstable : (prefixWord ++ tailWord_2929239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929239).length < 2 ^ (prefixWord ++ tailWord_2929239).sum := by decide
  have hdescent : baseEnd_2929239 < baseStart_2929239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929252 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2929252 : Nat := 118140960795 + 2929252 * 2 ^ 59
def prefixEnd_2929252 : Nat := 4983230072969 + 3 ^ 40 * 2929252 * 2
def baseEnd_2929252 : Nat := 1504114234144078521778621

theorem tailTrace_2929252 : CollatzResearch.WordTrace tailWord_2929252 prefixEnd_2929252 1504114234144078521778621 := by
  unfold tailWord_2929252
  simp only [CollatzResearch.WordTrace]
  refine ⟨53419298791913877628835005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71225731722551836838446673 53419298791913877628835005)
  ·
    refine ⟨20032237046967704110813127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53419298791913877628835005 20032237046967704110813127)
    ·
      refine ⟨30048355570451556166219691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032237046967704110813127 30048355570451556166219691)
      ·
        refine ⟨45072533355677334249329537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30048355570451556166219691 45072533355677334249329537)
        ·
          refine ⟨33804400016758000686997153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45072533355677334249329537 33804400016758000686997153)
          ·
            refine ⟨25353300012568500515247865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33804400016758000686997153 25353300012568500515247865)
            ·
              refine ⟨19014975009426375386435899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25353300012568500515247865 19014975009426375386435899)
              ·
                refine ⟨28522462514139563079653849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19014975009426375386435899 28522462514139563079653849)
                ·
                  refine ⟨21391846885604672309740387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28522462514139563079653849 21391846885604672309740387)
                  ·
                    refine ⟨32087770328407008464610581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21391846885604672309740387 32087770328407008464610581)
                    ·
                      refine ⟨1504114234144078521778621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32087770328407008464610581 1504114234144078521778621)
                      ·
                        rfl

theorem cell23_2929252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2929252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929252 prefixEnd_2929252 := by exact prefixLift 2929252
  have htrace : WordTrace (prefixWord ++ tailWord_2929252) baseStart_2929252 baseEnd_2929252 := by
    simpa [prefixWord, tailWord_2929252, baseEnd_2929252] using wordTrace_append hprefix tailTrace_2929252
  have hstable : (prefixWord ++ tailWord_2929252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929252).length < 2 ^ (prefixWord ++ tailWord_2929252).sum := by decide
  have hdescent : baseEnd_2929252 < baseStart_2929252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929299 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 5, 2]
def baseStart_2929299 : Nat := 118140960795 + 2929299 * 2 ^ 59
def prefixEnd_2929299 : Nat := 4983230072969 + 3 ^ 40 * 2929299 * 2
def baseEnd_2929299 : Nat := 1504138367734839837890905

theorem tailTrace_2929299 : CollatzResearch.WordTrace tailWord_2929299 prefixEnd_2929299 1504138367734839837890905 := by
  unfold tailWord_2929299
  simp only [CollatzResearch.WordTrace]
  refine ⟨106840311814657482284630951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71226874543104988189753967 106840311814657482284630951)
  ·
    refine ⟨160260467721986223426946427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106840311814657482284630951 160260467721986223426946427)
    ·
      refine ⟨240390701582979335140419641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160260467721986223426946427 240390701582979335140419641)
      ·
        refine ⟨180293026187234501355314731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240390701582979335140419641 180293026187234501355314731)
        ·
          refine ⟨270439539280851752032972097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180293026187234501355314731 270439539280851752032972097)
          ·
            refine ⟨202829654460638814024729073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270439539280851752032972097 202829654460638814024729073)
            ·
              refine ⟨152122240845479110518546805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202829654460638814024729073 152122240845479110518546805)
              ·
                refine ⟨14261460079263666611113763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152122240845479110518546805 14261460079263666611113763)
                ·
                  refine ⟨21392190118895499916670645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14261460079263666611113763 21392190118895499916670645)
                  ·
                    refine ⟨2005517823646453117187873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21392190118895499916670645 2005517823646453117187873)
                    ·
                      refine ⟨1504138367734839837890905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005517823646453117187873 1504138367734839837890905)
                      ·
                        rfl

theorem cell23_2929299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 5, 2].length) (baseStart_2929299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929299 prefixEnd_2929299 := by exact prefixLift 2929299
  have htrace : WordTrace (prefixWord ++ tailWord_2929299) baseStart_2929299 baseEnd_2929299 := by
    simpa [prefixWord, tailWord_2929299, baseEnd_2929299] using wordTrace_append hprefix tailTrace_2929299
  have hstable : (prefixWord ++ tailWord_2929299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929299).length < 2 ^ (prefixWord ++ tailWord_2929299).sum := by decide
  have hdescent : baseEnd_2929299 < baseStart_2929299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929300 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2929300 : Nat := 118140960795 + 2929300 * 2 ^ 59
def prefixEnd_2929300 : Nat := 4983230072969 + 3 ^ 40 * 2929300 * 2
def baseEnd_2929300 : Nat := 501379627071831444659467

theorem tailTrace_2929300 : CollatzResearch.WordTrace tailWord_2929300 prefixEnd_2929300 501379627071831444659467 := by
  unfold tailWord_2929300
  simp only [CollatzResearch.WordTrace]
  refine ⟨53420174143826929727708677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71226898858435906303611569 53420174143826929727708677)
  ·
    refine ⟨10016282651967549323945377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53420174143826929727708677 10016282651967549323945377)
    ·
      refine ⟨7512211988975661992959033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10016282651967549323945377 7512211988975661992959033)
      ·
        refine ⟨5634158991731746494719275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7512211988975661992959033 5634158991731746494719275)
        ·
          refine ⟨8451238487597619742078913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634158991731746494719275 8451238487597619742078913)
          ·
            refine ⟨6338428865698214806559185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8451238487597619742078913 6338428865698214806559185)
            ·
              refine ⟨4753821649273661104919389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338428865698214806559185 4753821649273661104919389)
              ·
                refine ⟨1782683118477622914344771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4753821649273661104919389 1782683118477622914344771)
                ·
                  refine ⟨2674024677716434371517157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782683118477622914344771 2674024677716434371517157)
                  ·
                    refine ⟨501379627071831444659467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674024677716434371517157 501379627071831444659467)
                    ·
                      rfl

theorem cell23_2929300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2929300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929300 prefixEnd_2929300 := by exact prefixLift 2929300
  have htrace : WordTrace (prefixWord ++ tailWord_2929300) baseStart_2929300 baseEnd_2929300 := by
    simpa [prefixWord, tailWord_2929300, baseEnd_2929300] using wordTrace_append hprefix tailTrace_2929300
  have hstable : (prefixWord ++ tailWord_2929300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929300).length < 2 ^ (prefixWord ++ tailWord_2929300).sum := by decide
  have hdescent : baseEnd_2929300 < baseStart_2929300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929313 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 6]
def baseStart_2929313 : Nat := 118140960795 + 2929313 * 2 ^ 59
def prefixEnd_2929313 : Nat := 4983230072969 + 3 ^ 40 * 2929313 * 2
def baseEnd_2929313 : Nat := 167127284051555864790649

theorem tailTrace_2929313 : CollatzResearch.WordTrace tailWord_2929313 prefixEnd_2929313 167127284051555864790649 := by
  unfold tailWord_2929313
  simp only [CollatzResearch.WordTrace]
  refine ⟨106840822436606762675640593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71227214957737841783760395 106840822436606762675640593)
  ·
    refine ⟨80130616827455072006730445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106840822436606762675640593 80130616827455072006730445)
    ·
      refine ⟨30048981310295652002523917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80130616827455072006730445 30048981310295652002523917)
      ·
        refine ⟨11268367991360869500946469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30048981310295652002523917 11268367991360869500946469)
        ·
          refine ⟨2112818998380163031427463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11268367991360869500946469 2112818998380163031427463)
          ·
            refine ⟨3169228497570244547141195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112818998380163031427463 3169228497570244547141195)
            ·
              refine ⟨4753842746355366820711793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3169228497570244547141195 4753842746355366820711793)
              ·
                refine ⟨3565382059766525115533845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753842746355366820711793 3565382059766525115533845)
                ·
                  refine ⟨167127284051555864790649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3565382059766525115533845 167127284051555864790649)
                  ·
                    rfl

theorem cell23_2929313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_2929313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929313 prefixEnd_2929313 := by exact prefixLift 2929313
  have htrace : WordTrace (prefixWord ++ tailWord_2929313) baseStart_2929313 baseEnd_2929313 := by
    simpa [prefixWord, tailWord_2929313, baseEnd_2929313] using wordTrace_append hprefix tailTrace_2929313
  have hstable : (prefixWord ++ tailWord_2929313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929313).length < 2 ^ (prefixWord ++ tailWord_2929313).sum := by decide
  have hdescent : baseEnd_2929313 < baseStart_2929313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929316 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_2929316 : Nat := 118140960795 + 2929316 * 2 ^ 59
def prefixEnd_2929316 : Nat := 4983230072969 + 3 ^ 40 * 2929316 * 2
def baseEnd_2929316 : Nat := 1504147096905966271378327

theorem tailTrace_2929316 : CollatzResearch.WordTrace tailWord_2929316 prefixEnd_2929316 1504147096905966271378327 := by
  unfold tailWord_2929316
  simp only [CollatzResearch.WordTrace]
  refine ⟨53420465927797947093999901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71227287903730596125333201 53420465927797947093999901)
  ·
    refine ⟨20032674722924230160249963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53420465927797947093999901 20032674722924230160249963)
    ·
      refine ⟨30049012084386345240374945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032674722924230160249963 30049012084386345240374945)
      ·
        refine ⟨22536759063289758930281209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30049012084386345240374945 22536759063289758930281209)
        ·
          refine ⟨16902569297467319197710907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22536759063289758930281209 16902569297467319197710907)
          ·
            refine ⟨25353853946200978796566361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16902569297467319197710907 25353853946200978796566361)
            ·
              refine ⟨19015390459650734097424771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25353853946200978796566361 19015390459650734097424771)
              ·
                refine ⟨28523085689476101146137157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19015390459650734097424771 28523085689476101146137157)
                ·
                  refine ⟨5348078566776768964900717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28523085689476101146137157 5348078566776768964900717)
                  ·
                    refine ⟨2005529462541288361837769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5348078566776768964900717 2005529462541288361837769)
                    ·
                      refine ⟨1504147096905966271378327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005529462541288361837769 1504147096905966271378327)
                      ·
                        rfl

theorem cell23_2929316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_2929316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929316 prefixEnd_2929316 := by exact prefixLift 2929316
  have htrace : WordTrace (prefixWord ++ tailWord_2929316) baseStart_2929316 baseEnd_2929316 := by
    simpa [prefixWord, tailWord_2929316, baseEnd_2929316] using wordTrace_append hprefix tailTrace_2929316
  have hstable : (prefixWord ++ tailWord_2929316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929316).length < 2 ^ (prefixWord ++ tailWord_2929316).sum := by decide
  have hdescent : baseEnd_2929316 < baseStart_2929316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929356 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_2929356 : Nat := 118140960795 + 2929356 * 2 ^ 59
def prefixEnd_2929356 : Nat := 4983230072969 + 3 ^ 40 * 2929356 * 2
def baseEnd_2929356 : Nat := 501389212044048704959381

theorem tailTrace_2929356 : CollatzResearch.WordTrace tailWord_2929356 prefixEnd_2929356 501389212044048704959381 := by
  unfold tailWord_2929356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53421195387725490509727961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71228260516967320679637281 53421195387725490509727961)
  ·
    refine ⟨40065896540794117882295971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53421195387725490509727961 40065896540794117882295971)
    ·
      refine ⟨60098844811191176823443957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40065896540794117882295971 60098844811191176823443957)
      ·
        refine ⟨5634266701049172827197871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60098844811191176823443957 5634266701049172827197871)
        ·
          refine ⟨8451400051573759240796807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634266701049172827197871 8451400051573759240796807)
          ·
            refine ⟨12677100077360638861195211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451400051573759240796807 12677100077360638861195211)
            ·
              refine ⟨19015650116040958291792817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677100077360638861195211 19015650116040958291792817)
              ·
                refine ⟨14261737587030718718844613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19015650116040958291792817 14261737587030718718844613)
                ·
                  refine ⟨2674075797568259759783365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14261737587030718718844613 2674075797568259759783365)
                  ·
                    refine ⟨501389212044048704959381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674075797568259759783365 501389212044048704959381)
                    ·
                      rfl

theorem cell23_2929356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_2929356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929356 prefixEnd_2929356 := by exact prefixLift 2929356
  have htrace : WordTrace (prefixWord ++ tailWord_2929356) baseStart_2929356 baseEnd_2929356 := by
    simpa [prefixWord, tailWord_2929356, baseEnd_2929356] using wordTrace_append hprefix tailTrace_2929356
  have hstable : (prefixWord ++ tailWord_2929356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929356).length < 2 ^ (prefixWord ++ tailWord_2929356).sum := by decide
  have hdescent : baseEnd_2929356 < baseStart_2929356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929380 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_2929380 : Nat := 118140960795 + 2929380 * 2 ^ 59
def prefixEnd_2929380 : Nat := 4983230072969 + 3 ^ 40 * 2929380 * 2
def baseEnd_2929380 : Nat := 1504179959667854020978033

theorem tailTrace_2929380 : CollatzResearch.WordTrace tailWord_2929380 prefixEnd_2929380 1504179959667854020978033 := by
  unfold tailWord_2929380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53421633063682016559164797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71228844084909355412219729 53421633063682016559164797)
  ·
    refine ⟨20033112398880756209686799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53421633063682016559164797 20033112398880756209686799)
    ·
      refine ⟨30049668598321134314530199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20033112398880756209686799 30049668598321134314530199)
      ·
        refine ⟨45074502897481701471795299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30049668598321134314530199 45074502897481701471795299)
        ·
          refine ⟨67611754346222552207692949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45074502897481701471795299 67611754346222552207692949)
          ·
            refine ⟨3169300984979182134735607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67611754346222552207692949 3169300984979182134735607)
            ·
              refine ⟨4753951477468773202103411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3169300984979182134735607 4753951477468773202103411)
              ·
                refine ⟨7130927216203159803155117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753951477468773202103411 7130927216203159803155117)
                ·
                  refine ⟨2674097706076184926183169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7130927216203159803155117 2674097706076184926183169)
                  ·
                    refine ⟨2005573279557138694637377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674097706076184926183169 2005573279557138694637377)
                    ·
                      refine ⟨1504179959667854020978033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005573279557138694637377 1504179959667854020978033)
                      ·
                        rfl

theorem cell23_2929380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_2929380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929380 prefixEnd_2929380 := by exact prefixLift 2929380
  have htrace : WordTrace (prefixWord ++ tailWord_2929380) baseStart_2929380 baseEnd_2929380 := by
    simpa [prefixWord, tailWord_2929380, baseEnd_2929380] using wordTrace_append hprefix tailTrace_2929380
  have hstable : (prefixWord ++ tailWord_2929380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929380).length < 2 ^ (prefixWord ++ tailWord_2929380).sum := by decide
  have hdescent : baseEnd_2929380 < baseStart_2929380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929389 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2929389 : Nat := 118140960795 + 2929389 * 2 ^ 59
def prefixEnd_2929389 : Nat := 4983230072969 + 3 ^ 40 * 2929389 * 2
def baseEnd_2929389 : Nat := 1504184580993744485765491

theorem tailTrace_2929389 : CollatzResearch.WordTrace tailWord_2929389 prefixEnd_2929389 1504184580993744485765491 := by
  unfold tailWord_2929389
  simp only [CollatzResearch.WordTrace]
  refine ⟨106843594384331427655407221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71229062922887618436938147 106843594384331427655407221)
  ·
    refine ⟨10016586973531071342694427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106843594384331427655407221 10016586973531071342694427)
    ·
      refine ⟨15024880460296607014041641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10016586973531071342694427 15024880460296607014041641)
      ·
        refine ⟨11268660345222455260531231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15024880460296607014041641 11268660345222455260531231)
        ·
          refine ⟨16902990517833682890796847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268660345222455260531231 16902990517833682890796847)
          ·
            refine ⟨25354485776750524336195271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16902990517833682890796847 25354485776750524336195271)
            ·
              refine ⟨38031728665125786504292907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25354485776750524336195271 38031728665125786504292907)
              ·
                refine ⟨57047592997688679756439361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38031728665125786504292907 57047592997688679756439361)
                ·
                  refine ⟨42785694748266509817329521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57047592997688679756439361 42785694748266509817329521)
                  ·
                    refine ⟨32089271061199882362997141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42785694748266509817329521 32089271061199882362997141)
                    ·
                      refine ⟨1504184580993744485765491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32089271061199882362997141 1504184580993744485765491)
                      ·
                        rfl

theorem cell23_2929389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2929389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929389 prefixEnd_2929389 := by exact prefixLift 2929389
  have htrace : WordTrace (prefixWord ++ tailWord_2929389) baseStart_2929389 baseEnd_2929389 := by
    simpa [prefixWord, tailWord_2929389, baseEnd_2929389] using wordTrace_append hprefix tailTrace_2929389
  have hstable : (prefixWord ++ tailWord_2929389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929389).length < 2 ^ (prefixWord ++ tailWord_2929389).sum := by decide
  have hdescent : baseEnd_2929389 < baseStart_2929389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929390 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2929390 : Nat := 118140960795 + 2929390 * 2 ^ 59
def prefixEnd_2929390 : Nat := 4983230072969 + 3 ^ 40 * 2929390 * 2
def baseEnd_2929390 : Nat := 501395031491466327284329

theorem tailTrace_2929390 : CollatzResearch.WordTrace tailWord_2929390 prefixEnd_2929390 501395031491466327284329 := by
  unfold tailWord_2929390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13355453857165975603274203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71229087238218536550795749 13355453857165975603274203)
  ·
    refine ⟨20033180785748963404911305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13355453857165975603274203 20033180785748963404911305)
    ·
      refine ⟨15024885589311722553683479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20033180785748963404911305 15024885589311722553683479)
      ·
        refine ⟨22537328383967583830525219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15024885589311722553683479 22537328383967583830525219)
        ·
          refine ⟨33805992575951375745787829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22537328383967583830525219 33805992575951375745787829)
          ·
            refine ⟨3169311803995441476167609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33805992575951375745787829 3169311803995441476167609)
            ·
              refine ⟨2376983852996581107125707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169311803995441476167609 2376983852996581107125707)
              ·
                refine ⟨3565475779494871660688561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376983852996581107125707 3565475779494871660688561)
                ·
                  refine ⟨2674106834621153745516421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565475779494871660688561 2674106834621153745516421)
                  ·
                    refine ⟨501395031491466327284329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674106834621153745516421 501395031491466327284329)
                    ·
                      rfl

theorem cell23_2929390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2929390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929390 prefixEnd_2929390 := by exact prefixLift 2929390
  have htrace : WordTrace (prefixWord ++ tailWord_2929390) baseStart_2929390 baseEnd_2929390 := by
    simpa [prefixWord, tailWord_2929390, baseEnd_2929390] using wordTrace_append hprefix tailTrace_2929390
  have hstable : (prefixWord ++ tailWord_2929390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929390).length < 2 ^ (prefixWord ++ tailWord_2929390).sum := by decide
  have hdescent : baseEnd_2929390 < baseStart_2929390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929429 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2929429 : Nat := 118140960795 + 2929429 * 2 ^ 59
def prefixEnd_2929429 : Nat := 4983230072969 + 3 ^ 40 * 2929429 * 2
def baseEnd_2929429 : Nat := 501401706739974776421769

theorem tailTrace_2929429 : CollatzResearch.WordTrace tailWord_2929429 prefixEnd_2929429 501401706739974776421769 := by
  unfold tailWord_2929429
  simp only [CollatzResearch.WordTrace]
  refine ⟨106845053304186514486863341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71230035536124342991242227 106845053304186514486863341)
  ·
    refine ⟨40066894989069942932573753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106845053304186514486863341 40066894989069942932573753)
    ·
      refine ⟨30050171241802457199430315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40066894989069942932573753 30050171241802457199430315)
      ·
        refine ⟨45075256862703685799145473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30050171241802457199430315 45075256862703685799145473)
        ·
          refine ⟨33806442647027764349359105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45075256862703685799145473 33806442647027764349359105)
          ·
            refine ⟨25354831985270823262019329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33806442647027764349359105 25354831985270823262019329)
            ·
              refine ⟨19016123988953117446514497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25354831985270823262019329 19016123988953117446514497)
              ·
                refine ⟨14262092991714838084885873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19016123988953117446514497 14262092991714838084885873)
                ·
                  refine ⟨10696569743786128563664405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14262092991714838084885873 10696569743786128563664405)
                  ·
                    refine ⟨501401706739974776421769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10696569743786128563664405 501401706739974776421769)
                    ·
                      rfl

theorem cell23_2929429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2929429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929429 prefixEnd_2929429 := by exact prefixLift 2929429
  have htrace : WordTrace (prefixWord ++ tailWord_2929429) baseStart_2929429 baseEnd_2929429 := by
    simpa [prefixWord, tailWord_2929429, baseEnd_2929429] using wordTrace_append hprefix tailTrace_2929429
  have hstable : (prefixWord ++ tailWord_2929429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929429).length < 2 ^ (prefixWord ++ tailWord_2929429).sum := by decide
  have hdescent : baseEnd_2929429 < baseStart_2929429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929431 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2929431 : Nat := 118140960795 + 2929431 * 2 ^ 59
def prefixEnd_2929431 : Nat := 4983230072969 + 3 ^ 40 * 2929431 * 2
def baseEnd_2929431 : Nat := 1504206147181233321440299

theorem tailTrace_2929431 : CollatzResearch.WordTrace tailWord_2929431 prefixEnd_2929431 1504206147181233321440299 := by
  unfold tailWord_2929431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106845126250179268828436147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71230084166786179218957431 106845126250179268828436147)
  ·
    refine ⟨160267689375268903242654221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106845126250179268828436147 160267689375268903242654221)
    ·
      refine ⟨60100383515725838715995333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160267689375268903242654221 60100383515725838715995333)
      ·
        refine ⟨11268821909198594759249125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60100383515725838715995333 11268821909198594759249125)
        ·
          refine ⟨2112904107974736517359211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11268821909198594759249125 2112904107974736517359211)
          ·
            refine ⟨3169356161962104776038817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112904107974736517359211 3169356161962104776038817)
            ·
              refine ⟨2377017121471578582029113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169356161962104776038817 2377017121471578582029113)
              ·
                refine ⟨1782762841103683936521835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377017121471578582029113 1782762841103683936521835)
                ·
                  refine ⟨2674144261655525904782753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782762841103683936521835 2674144261655525904782753)
                  ·
                    refine ⟨2005608196241644428587065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674144261655525904782753 2005608196241644428587065)
                    ·
                      refine ⟨1504206147181233321440299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005608196241644428587065 1504206147181233321440299)
                      ·
                        rfl

theorem cell23_2929431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2929431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929431 prefixEnd_2929431 := by exact prefixLift 2929431
  have htrace : WordTrace (prefixWord ++ tailWord_2929431) baseStart_2929431 baseEnd_2929431 := by
    simpa [prefixWord, tailWord_2929431, baseEnd_2929431] using wordTrace_append hprefix tailTrace_2929431
  have hstable : (prefixWord ++ tailWord_2929431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929431).length < 2 ^ (prefixWord ++ tailWord_2929431).sum := by decide
  have hdescent : baseEnd_2929431 < baseStart_2929431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929449 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2929449 : Nat := 118140960795 + 2929449 * 2 ^ 59
def prefixEnd_2929449 : Nat := 4983230072969 + 3 ^ 40 * 2929449 * 2
def baseEnd_2929449 : Nat := 1504215389833014251015215

theorem tailTrace_2929449 : CollatzResearch.WordTrace tailWord_2929449 prefixEnd_2929449 1504215389833014251015215 := by
  unfold tailWord_2929449
  simp only [CollatzResearch.WordTrace]
  refine ⟨106845782764114057902591401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71230521842742705268394267 106845782764114057902591401)
  ·
    refine ⟨80134337073085543426943551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106845782764114057902591401 80134337073085543426943551)
    ·
      refine ⟨120201505609628315140415327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80134337073085543426943551 120201505609628315140415327)
      ·
        refine ⟨180302258414442472710622991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120201505609628315140415327 180302258414442472710622991)
        ·
          refine ⟨270453387621663709065934487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180302258414442472710622991 270453387621663709065934487)
          ·
            refine ⟨405680081432495563598901731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270453387621663709065934487 405680081432495563598901731)
            ·
              refine ⟨608520122148743345398352597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405680081432495563598901731 608520122148743345398352597)
              ·
                refine ⟨14262190362861172157773889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 608520122148743345398352597 14262190362861172157773889)
                ·
                  refine ⟨10696642772145879118330417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14262190362861172157773889 10696642772145879118330417)
                  ·
                    refine ⟨8022482079109409338747813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10696642772145879118330417 8022482079109409338747813)
                    ·
                      refine ⟨1504215389833014251015215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8022482079109409338747813 1504215389833014251015215)
                      ·
                        rfl

theorem cell23_2929449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2929449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929449 prefixEnd_2929449 := by exact prefixLift 2929449
  have htrace : WordTrace (prefixWord ++ tailWord_2929449) baseStart_2929449 baseEnd_2929449 := by
    simpa [prefixWord, tailWord_2929449, baseEnd_2929449] using wordTrace_append hprefix tailTrace_2929449
  have hstable : (prefixWord ++ tailWord_2929449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929449).length < 2 ^ (prefixWord ++ tailWord_2929449).sum := by decide
  have hdescent : baseEnd_2929449 < baseStart_2929449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929459 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 9]
def baseStart_2929459 : Nat := 118140960795 + 2929459 * 2 ^ 59
def prefixEnd_2929459 : Nat := 4983230072969 + 3 ^ 40 * 2929459 * 2
def baseEnd_2929459 : Nat := 167135613848839912432241

theorem tailTrace_2929459 : CollatzResearch.WordTrace tailWord_2929459 prefixEnd_2929459 167135613848839912432241 := by
  unfold tailWord_2929459
  simp only [CollatzResearch.WordTrace]
  refine ⟨106846147494077829610455431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71230764996051886406970287 106846147494077829610455431)
  ·
    refine ⟨160269221241116744415683147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106846147494077829610455431 160269221241116744415683147)
    ·
      refine ⟨240403831861675116623524721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160269221241116744415683147 240403831861675116623524721)
      ·
        refine ⟨180302873896256337467643541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240403831861675116623524721 180302873896256337467643541)
        ·
          refine ⟨8451697213887015818795791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180302873896256337467643541 8451697213887015818795791)
          ·
            refine ⟨12677545820830523728193687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451697213887015818795791 12677545820830523728193687)
            ·
              refine ⟨19016318731245785592290531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677545820830523728193687 19016318731245785592290531)
              ·
                refine ⟨28524478096868678388435797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19016318731245785592290531 28524478096868678388435797)
                ·
                  refine ⟨167135613848839912432241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28524478096868678388435797 167135613848839912432241)
                  ·
                    rfl

theorem cell23_2929459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 9].length) (baseStart_2929459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929459 prefixEnd_2929459 := by exact prefixLift 2929459
  have htrace : WordTrace (prefixWord ++ tailWord_2929459) baseStart_2929459 baseEnd_2929459 := by
    simpa [prefixWord, tailWord_2929459, baseEnd_2929459] using wordTrace_append hprefix tailTrace_2929459
  have hstable : (prefixWord ++ tailWord_2929459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929459).length < 2 ^ (prefixWord ++ tailWord_2929459).sum := by decide
  have hdescent : baseEnd_2929459 < baseStart_2929459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929496 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_2929496 : Nat := 118140960795 + 2929496 * 2 ^ 59
def prefixEnd_2929496 : Nat := 4983230072969 + 3 ^ 40 * 2929496 * 2
def baseEnd_2929496 : Nat := 1504239523423775567127499

theorem tailTrace_2929496 : CollatzResearch.WordTrace tailWord_2929496 prefixEnd_2929496 1504239523423775567127499 := by
  unfold tailWord_2929496
  simp only [CollatzResearch.WordTrace]
  refine ⟨53423748497471892464776171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71231664663295856619701561 53423748497471892464776171)
  ·
    refine ⟨80135622746207838697164257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53423748497471892464776171 80135622746207838697164257)
    ·
      refine ⟨60101717059655879022873193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80135622746207838697164257 60101717059655879022873193)
      ·
        refine ⟨45076287794741909267154895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60101717059655879022873193 45076287794741909267154895)
        ·
          refine ⟨67614431692112863900732343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45076287794741909267154895 67614431692112863900732343)
          ·
            refine ⟨101421647538169295851098515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67614431692112863900732343 101421647538169295851098515)
            ·
              refine ⟨152132471307253943776647773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101421647538169295851098515 152132471307253943776647773)
              ·
                refine ⟨57049676740220228916242915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152132471307253943776647773 57049676740220228916242915)
                ·
                  refine ⟨85574515110330343374364373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57049676740220228916242915 85574515110330343374364373)
                  ·
                    refine ⟨2005652697898367422836665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85574515110330343374364373 2005652697898367422836665)
                    ·
                      refine ⟨1504239523423775567127499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005652697898367422836665 1504239523423775567127499)
                      ·
                        rfl

theorem cell23_2929496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_2929496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929496 prefixEnd_2929496 := by exact prefixLift 2929496
  have htrace : WordTrace (prefixWord ++ tailWord_2929496) baseStart_2929496 baseEnd_2929496 := by
    simpa [prefixWord, tailWord_2929496, baseEnd_2929496] using wordTrace_append hprefix tailTrace_2929496
  have hstable : (prefixWord ++ tailWord_2929496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929496).length < 2 ^ (prefixWord ++ tailWord_2929496).sum := by decide
  have hdescent : baseEnd_2929496 < baseStart_2929496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929543 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2929543 : Nat := 118140960795 + 2929543 * 2 ^ 59
def prefixEnd_2929543 : Nat := 4983230072969 + 3 ^ 40 * 2929543 * 2
def baseEnd_2929543 : Nat := 1504263657014536883239783

theorem tailTrace_2929543 : CollatzResearch.WordTrace tailWord_2929543 prefixEnd_2929543 1504263657014536883239783 := by
  unfold tailWord_2929543
  simp only [CollatzResearch.WordTrace]
  refine ⟨106849211225773511956513283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71232807483849007971008855 106849211225773511956513283)
  ·
    refine ⟨160273816838660267934769925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106849211225773511956513283 160273816838660267934769925)
    ·
      refine ⟨30051340657248800237769361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160273816838660267934769925 30051340657248800237769361)
      ·
        refine ⟨22538505492936600178327021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30051340657248800237769361 22538505492936600178327021)
        ·
          refine ⟨8451939559851225066872633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22538505492936600178327021 8451939559851225066872633)
          ·
            refine ⟨6338954669888418800154475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8451939559851225066872633 6338954669888418800154475)
            ·
              refine ⟨9508432004832628200231713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338954669888418800154475 9508432004832628200231713)
              ·
                refine ⟨7131324003624471150173785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9508432004832628200231713 7131324003624471150173785)
                ·
                  refine ⟨5348493002718353362630339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7131324003624471150173785 5348493002718353362630339)
                  ·
                    refine ⟨8022739504077530043945509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5348493002718353362630339 8022739504077530043945509)
                    ·
                      refine ⟨1504263657014536883239783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8022739504077530043945509 1504263657014536883239783)
                      ·
                        rfl

theorem cell23_2929543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2929543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929543 prefixEnd_2929543 := by exact prefixLift 2929543
  have htrace : WordTrace (prefixWord ++ tailWord_2929543) baseStart_2929543 baseEnd_2929543 := by
    simpa [prefixWord, tailWord_2929543, baseEnd_2929543] using wordTrace_append hprefix tailTrace_2929543
  have hstable : (prefixWord ++ tailWord_2929543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929543).length < 2 ^ (prefixWord ++ tailWord_2929543).sum := by decide
  have hdescent : baseEnd_2929543 < baseStart_2929543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929579 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 9]
def baseStart_2929579 : Nat := 118140960795 + 2929579 * 2 ^ 59
def prefixEnd_2929579 : Nat := 4983230072969 + 3 ^ 40 * 2929579 * 2
def baseEnd_2929579 : Nat := 501427380772699580796539

theorem tailTrace_2929579 : CollatzResearch.WordTrace tailWord_2929579 prefixEnd_2929579 501427380772699580796539 := by
  unfold tailWord_2929579
  simp only [CollatzResearch.WordTrace]
  refine ⟨106850524253643090104823791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71233682835762060069882527 106850524253643090104823791)
  ·
    refine ⟨160275786380464635157235687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106850524253643090104823791 160275786380464635157235687)
    ·
      refine ⟨240413679570696952735853531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160275786380464635157235687 240413679570696952735853531)
      ·
        refine ⟨360620519356045429103780297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240413679570696952735853531 360620519356045429103780297)
        ·
          refine ⟨270465389517034071827835223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360620519356045429103780297 270465389517034071827835223)
          ·
            refine ⟨405698084275551107741752835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270465389517034071827835223 405698084275551107741752835)
            ·
              refine ⟨608547126413326661612629253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405698084275551107741752835 608547126413326661612629253)
              ·
                refine ⟨114102586202498749052367985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608547126413326661612629253 114102586202498749052367985)
                ·
                  refine ⟨85576939651874061789275989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114102586202498749052367985 85576939651874061789275989)
                  ·
                    refine ⟨501427380772699580796539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85576939651874061789275989 501427380772699580796539)
                    ·
                      rfl

theorem cell23_2929579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_2929579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929579 prefixEnd_2929579 := by exact prefixLift 2929579
  have htrace : WordTrace (prefixWord ++ tailWord_2929579) baseStart_2929579 baseEnd_2929579 := by
    simpa [prefixWord, tailWord_2929579, baseEnd_2929579] using wordTrace_append hprefix tailTrace_2929579
  have hstable : (prefixWord ++ tailWord_2929579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929579).length < 2 ^ (prefixWord ++ tailWord_2929579).sum := by decide
  have hdescent : baseEnd_2929579 < baseStart_2929579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929604 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2929604 : Nat := 118140960795 + 2929604 * 2 ^ 59
def prefixEnd_2929604 : Nat := 4983230072969 + 3 ^ 40 * 2929604 * 2
def baseEnd_2929604 : Nat := 501431659778153714859001

theorem tailTrace_2929604 : CollatzResearch.WordTrace tailWord_2929604 prefixEnd_2929604 501431659778153714859001 := by
  unfold tailWord_2929604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53425718039276259687241933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71234290719035012916322577 53425718039276259687241933)
  ·
    refine ⟨20034644264728597382715725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53425718039276259687241933 20034644264728597382715725)
    ·
      refine ⟨7512991599273224018518397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20034644264728597382715725 7512991599273224018518397)
      ·
        refine ⟨2817371849727459006944399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7512991599273224018518397 2817371849727459006944399)
        ·
          refine ⟨4226057774591188510416599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817371849727459006944399 4226057774591188510416599)
          ·
            refine ⟨6339086661886782765624899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226057774591188510416599 6339086661886782765624899)
            ·
              refine ⟨9508629992830174148437349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6339086661886782765624899 9508629992830174148437349)
              ·
                refine ⟨1782868123655657652832003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9508629992830174148437349 1782868123655657652832003)
                ·
                  refine ⟨2674302185483486479248005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782868123655657652832003 2674302185483486479248005)
                  ·
                    refine ⟨501431659778153714859001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674302185483486479248005 501431659778153714859001)
                    ·
                      rfl

theorem cell23_2929604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2929604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929604 prefixEnd_2929604 := by exact prefixLift 2929604
  have htrace : WordTrace (prefixWord ++ tailWord_2929604) baseStart_2929604 baseEnd_2929604 := by
    simpa [prefixWord, tailWord_2929604, baseEnd_2929604] using wordTrace_append hprefix tailTrace_2929604
  have hstable : (prefixWord ++ tailWord_2929604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929604).length < 2 ^ (prefixWord ++ tailWord_2929604).sum := by decide
  have hdescent : baseEnd_2929604 < baseStart_2929604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929633 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2929633 : Nat := 118140960795 + 2929633 * 2 ^ 59
def prefixEnd_2929633 : Nat := 4983230072969 + 3 ^ 40 * 2929633 * 2
def baseEnd_2929633 : Nat := 1504309870273441531114369

theorem tailTrace_2929633 : CollatzResearch.WordTrace tailWord_2929633 prefixEnd_2929633 1504309870273441531114369 := by
  unfold tailWord_2929633
  simp only [CollatzResearch.WordTrace]
  refine ⟨106852493795447457327289553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71234995863631638218193035 106852493795447457327289553)
  ·
    refine ⟨80139370346585592995467165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106852493795447457327289553 80139370346585592995467165)
    ·
      refine ⟨30052263879969597373300187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80139370346585592995467165 30052263879969597373300187)
      ·
        refine ⟨45078395819954396059950281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30052263879969597373300187 45078395819954396059950281)
        ·
          refine ⟨33808796864965797044962711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45078395819954396059950281 33808796864965797044962711)
          ·
            refine ⟨50713195297448695567444067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33808796864965797044962711 50713195297448695567444067)
            ·
              refine ⟨76069792946173043351166101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50713195297448695567444067 76069792946173043351166101)
              ·
                refine ⟨3565771544351861407085911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76069792946173043351166101 3565771544351861407085911)
                ·
                  refine ⟨5348657316527792110628867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565771544351861407085911 5348657316527792110628867)
                  ·
                    refine ⟨8022985974791688165943301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5348657316527792110628867 8022985974791688165943301)
                    ·
                      refine ⟨1504309870273441531114369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8022985974791688165943301 1504309870273441531114369)
                      ·
                        rfl

theorem cell23_2929633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2929633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929633 prefixEnd_2929633 := by exact prefixLift 2929633
  have htrace : WordTrace (prefixWord ++ tailWord_2929633) baseStart_2929633 baseEnd_2929633 := by
    simpa [prefixWord, tailWord_2929633, baseEnd_2929633] using wordTrace_append hprefix tailTrace_2929633
  have hstable : (prefixWord ++ tailWord_2929633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929633).length < 2 ^ (prefixWord ++ tailWord_2929633).sum := by decide
  have hdescent : baseEnd_2929633 < baseStart_2929633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929636 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2929636 : Nat := 118140960795 + 2929636 * 2 ^ 59
def prefixEnd_2929636 : Nat := 4983230072969 + 3 ^ 40 * 2929636 * 2
def baseEnd_2929636 : Nat := 1504311410715405019376855

theorem tailTrace_2929636 : CollatzResearch.WordTrace tailWord_2929636 prefixEnd_2929636 1504311410715405019376855 := by
  unfold tailWord_2929636
  simp only [CollatzResearch.WordTrace]
  refine ⟨53426301607218294419824381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71235068809624392559765841 53426301607218294419824381)
  ·
    refine ⟨20034863102706860407434143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53426301607218294419824381 20034863102706860407434143)
    ·
      refine ⟨30052294654060290611151215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20034863102706860407434143 30052294654060290611151215)
      ·
        refine ⟨45078441981090435916726823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30052294654060290611151215 45078441981090435916726823)
        ·
          refine ⟨67617662971635653875090235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45078441981090435916726823 67617662971635653875090235)
          ·
            refine ⟨101426494457453480812635353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67617662971635653875090235 101426494457453480812635353)
            ·
              refine ⟨76069870843090110609476515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101426494457453480812635353 76069870843090110609476515)
              ·
                refine ⟨114104806264635165914214773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76069870843090110609476515 114104806264635165914214773)
                ·
                  refine ⟨10697325587309546804457635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114104806264635165914214773 10697325587309546804457635)
                  ·
                    refine ⟨16045988380964320206686453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10697325587309546804457635 16045988380964320206686453)
                    ·
                      refine ⟨1504311410715405019376855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16045988380964320206686453 1504311410715405019376855)
                      ·
                        rfl

theorem cell23_2929636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2929636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929636 prefixEnd_2929636 := by exact prefixLift 2929636
  have htrace : WordTrace (prefixWord ++ tailWord_2929636) baseStart_2929636 baseEnd_2929636 := by
    simpa [prefixWord, tailWord_2929636, baseEnd_2929636] using wordTrace_append hprefix tailTrace_2929636
  have hstable : (prefixWord ++ tailWord_2929636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929636).length < 2 ^ (prefixWord ++ tailWord_2929636).sum := by decide
  have hdescent : baseEnd_2929636 < baseStart_2929636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929637 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2929637 : Nat := 118140960795 + 2929637 * 2 ^ 59
def prefixEnd_2929637 : Nat := 4983230072969 + 3 ^ 40 * 2929637 * 2
def baseEnd_2929637 : Nat := 1504311924196059515464351

theorem tailTrace_2929637 : CollatzResearch.WordTrace tailWord_2929637 prefixEnd_2929637 1504311924196059515464351 := by
  unfold tailWord_2929637
  simp only [CollatzResearch.WordTrace]
  refine ⟨106852639687432966010435165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71235093124955310673623443 106852639687432966010435165)
  ·
    refine ⟨40069739882787362253913187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106852639687432966010435165 40069739882787362253913187)
    ·
      refine ⟨60104609824181043380869781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40069739882787362253913187 60104609824181043380869781)
      ·
        refine ⟨2817403585508486408478271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60104609824181043380869781 2817403585508486408478271)
        ·
          refine ⟨4226105378262729612717407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2817403585508486408478271 4226105378262729612717407)
          ·
            refine ⟨6339158067394094419076111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226105378262729612717407 6339158067394094419076111)
            ·
              refine ⟨9508737101091141628614167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6339158067394094419076111 9508737101091141628614167)
              ·
                refine ⟨14263105651636712442921251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9508737101091141628614167 14263105651636712442921251)
                ·
                  refine ⟨21394658477455068664381877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14263105651636712442921251 21394658477455068664381877)
                  ·
                    refine ⟨2005749232261412687285801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21394658477455068664381877 2005749232261412687285801)
                    ·
                      refine ⟨1504311924196059515464351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005749232261412687285801 1504311924196059515464351)
                      ·
                        rfl

theorem cell23_2929637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2929637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929637 prefixEnd_2929637 := by exact prefixLift 2929637
  have htrace : WordTrace (prefixWord ++ tailWord_2929637) baseStart_2929637 baseEnd_2929637 := by
    simpa [prefixWord, tailWord_2929637, baseEnd_2929637] using wordTrace_append hprefix tailTrace_2929637
  have hstable : (prefixWord ++ tailWord_2929637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929637).length < 2 ^ (prefixWord ++ tailWord_2929637).sum := by decide
  have hdescent : baseEnd_2929637 < baseStart_2929637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929660 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_2929660 : Nat := 118140960795 + 2929660 * 2 ^ 59
def prefixEnd_2929660 : Nat := 4983230072969 + 3 ^ 40 * 2929660 * 2
def baseEnd_2929660 : Nat := 501441244750370975158915

theorem tailTrace_2929660 : CollatzResearch.WordTrace tailWord_2929660 prefixEnd_2929660 501441244750370975158915 := by
  unfold tailWord_2929660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53426739283174820469261217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71235652377566427292348289 53426739283174820469261217)
  ·
    refine ⟨40070054462381115351945913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53426739283174820469261217 40070054462381115351945913)
    ·
      refine ⟨30052540846785836513959435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40070054462381115351945913 30052540846785836513959435)
      ·
        refine ⟨45078811270178754770939153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30052540846785836513959435 45078811270178754770939153)
        ·
          refine ⟨33809108452634066078204365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45078811270178754770939153 33809108452634066078204365)
          ·
            refine ⟨12678415669737774779326637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33809108452634066078204365 12678415669737774779326637)
            ·
              refine ⟨4754405876151665542247489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12678415669737774779326637 4754405876151665542247489)
              ·
                refine ⟨3565804407113749156685617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754405876151665542247489 3565804407113749156685617)
                ·
                  refine ⟨2674353305335311867514213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565804407113749156685617 2674353305335311867514213)
                  ·
                    refine ⟨501441244750370975158915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674353305335311867514213 501441244750370975158915)
                    ·
                      rfl

theorem cell23_2929660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_2929660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929660 prefixEnd_2929660 := by exact prefixLift 2929660
  have htrace : WordTrace (prefixWord ++ tailWord_2929660) baseStart_2929660 baseEnd_2929660 := by
    simpa [prefixWord, tailWord_2929660, baseEnd_2929660] using wordTrace_append hprefix tailTrace_2929660
  have hstable : (prefixWord ++ tailWord_2929660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929660).length < 2 ^ (prefixWord ++ tailWord_2929660).sum := by decide
  have hdescent : baseEnd_2929660 < baseStart_2929660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929687 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2929687 : Nat := 118140960795 + 2929687 * 2 ^ 59
def prefixEnd_2929687 : Nat := 4983230072969 + 3 ^ 40 * 2929687 * 2
def baseEnd_2929687 : Nat := 1504337598228784319839121

theorem tailTrace_2929687 : CollatzResearch.WordTrace tailWord_2929687 prefixEnd_2929687 1504337598228784319839121 := by
  unfold tailWord_2929687
  simp only [CollatzResearch.WordTrace]
  refine ⟨106854463337251824549755315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71236308891501216366503543 106854463337251824549755315)
  ·
    refine ⟨160281695005877736824632973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106854463337251824549755315 160281695005877736824632973)
    ·
      refine ⟨60105635627204151309237365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160281695005877736824632973 60105635627204151309237365)
      ·
        refine ⟨5634903340050389185241003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60105635627204151309237365 5634903340050389185241003)
        ·
          refine ⟨8452355010075583777861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634903340050389185241003 8452355010075583777861505)
          ·
            refine ⟨6339266257556687833396129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8452355010075583777861505 6339266257556687833396129)
            ·
              refine ⟨4754449693167515875047097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339266257556687833396129 4754449693167515875047097)
              ·
                refine ⟨3565837269875636906285323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754449693167515875047097 3565837269875636906285323)
                ·
                  refine ⟨5348755904813455359427985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565837269875636906285323 5348755904813455359427985)
                  ·
                    refine ⟨4011566928610091519570989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5348755904813455359427985 4011566928610091519570989)
                    ·
                      refine ⟨1504337598228784319839121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4011566928610091519570989 1504337598228784319839121)
                      ·
                        rfl

theorem cell23_2929687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2929687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929687 prefixEnd_2929687 := by exact prefixLift 2929687
  have htrace : WordTrace (prefixWord ++ tailWord_2929687) baseStart_2929687 baseEnd_2929687 := by
    simpa [prefixWord, tailWord_2929687, baseEnd_2929687] using wordTrace_append hprefix tailTrace_2929687
  have hstable : (prefixWord ++ tailWord_2929687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929687).length < 2 ^ (prefixWord ++ tailWord_2929687).sum := by decide
  have hdescent : baseEnd_2929687 < baseStart_2929687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929718 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_2929718 : Nat := 118140960795 + 2929718 * 2 ^ 59
def prefixEnd_2929718 : Nat := 4983230072969 + 3 ^ 40 * 2929718 * 2
def baseEnd_2929718 : Nat := 1504353516129073698551479

theorem tailTrace_2929718 : CollatzResearch.WordTrace tailWord_2929718 prefixEnd_2929718 1504353516129073698551479 := by
  unfold tailWord_2929718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678474625008719802758363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71237062666759677896089205 6678474625008719802758363)
  ·
    refine ⟨10017711937513079704137545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6678474625008719802758363 10017711937513079704137545)
    ·
      refine ⟨7513283953134809778103159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10017711937513079704137545 7513283953134809778103159)
      ·
        refine ⟨11269925929702214667154739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513283953134809778103159 11269925929702214667154739)
        ·
          refine ⟨16904888894553322000732109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11269925929702214667154739 16904888894553322000732109)
          ·
            refine ⟨6339333335457495750274541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16904888894553322000732109 6339333335457495750274541)
            ·
              refine ⟨2377250000796560906352953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6339333335457495750274541 2377250000796560906352953)
              ·
                refine ⟨1782937500597420679764715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377250000796560906352953 1782937500597420679764715)
                ·
                  refine ⟨2674406250896131019647073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782937500597420679764715 2674406250896131019647073)
                  ·
                    refine ⟨2005804688172098264735305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674406250896131019647073 2005804688172098264735305)
                    ·
                      refine ⟨1504353516129073698551479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005804688172098264735305 1504353516129073698551479)
                      ·
                        rfl

theorem cell23_2929718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_2929718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929718 prefixEnd_2929718 := by exact prefixLift 2929718
  have htrace : WordTrace (prefixWord ++ tailWord_2929718) baseStart_2929718 baseEnd_2929718 := by
    simpa [prefixWord, tailWord_2929718, baseEnd_2929718] using wordTrace_append hprefix tailTrace_2929718
  have hstable : (prefixWord ++ tailWord_2929718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929718).length < 2 ^ (prefixWord ++ tailWord_2929718).sum := by decide
  have hdescent : baseEnd_2929718 < baseStart_2929718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 8, 2]
def baseStart_2929723 : Nat := 118140960795 + 2929723 * 2 ^ 59
def prefixEnd_2929723 : Nat := 4983230072969 + 3 ^ 40 * 2929723 * 2
def baseEnd_2929723 : Nat := 1504356083532346178988955

theorem tailTrace_2929723 : CollatzResearch.WordTrace tailWord_2929723 prefixEnd_2929723 1504356083532346178988955 := by
  unfold tailWord_2929723
  simp only [CollatzResearch.WordTrace]
  refine ⟨106855776365121402698065823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71237184243414268465377215 106855776365121402698065823)
  ·
    refine ⟨160283664547682104047098735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106855776365121402698065823 160283664547682104047098735)
    ·
      refine ⟨240425496821523156070648103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160283664547682104047098735 240425496821523156070648103)
      ·
        refine ⟨360638245232284734105972155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240425496821523156070648103 360638245232284734105972155)
        ·
          refine ⟨540957367848427101158958233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360638245232284734105972155 540957367848427101158958233)
          ·
            refine ⟨405718025886320325869218675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540957367848427101158958233 405718025886320325869218675)
            ·
              refine ⟨608577038829480488803828013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405718025886320325869218675 608577038829480488803828013)
              ·
                refine ⟨228216389561055183301435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608577038829480488803828013 228216389561055183301435505)
                ·
                  refine ⟨171162292170791387476076629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228216389561055183301435505 171162292170791387476076629)
                  ·
                    refine ⟨2005808111376461571985273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 171162292170791387476076629 2005808111376461571985273)
                    ·
                      refine ⟨1504356083532346178988955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005808111376461571985273 1504356083532346178988955)
                      ·
                        rfl

theorem cell23_2929723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8, 2].length) (baseStart_2929723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929723 prefixEnd_2929723 := by exact prefixLift 2929723
  have htrace : WordTrace (prefixWord ++ tailWord_2929723) baseStart_2929723 baseEnd_2929723 := by
    simpa [prefixWord, tailWord_2929723, baseEnd_2929723] using wordTrace_append hprefix tailTrace_2929723
  have hstable : (prefixWord ++ tailWord_2929723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929723).length < 2 ^ (prefixWord ++ tailWord_2929723).sum := by decide
  have hdescent : baseEnd_2929723 < baseStart_2929723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929740 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_2929740 : Nat := 118140960795 + 2929740 * 2 ^ 59
def prefixEnd_2929740 : Nat := 4983230072969 + 3 ^ 40 * 2929740 * 2
def baseEnd_2929740 : Nat := 1504364812703472612476377

theorem tailTrace_2929740 : CollatzResearch.WordTrace tailWord_2929740 prefixEnd_2929740 1504364812703472612476377 := by
  unfold tailWord_2929740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53428198203029907300717337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71237597604039876400956449 53428198203029907300717337)
  ·
    refine ⟨40071148652272430475538003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53428198203029907300717337 40071148652272430475538003)
    ·
      refine ⟨60106722978408645713307005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40071148652272430475538003 60106722978408645713307005)
      ·
        refine ⟨22540021116903242142490127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60106722978408645713307005 22540021116903242142490127)
        ·
          refine ⟨33810031675354863213735191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22540021116903242142490127 33810031675354863213735191)
          ·
            refine ⟨50715047513032294820602787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33810031675354863213735191 50715047513032294820602787)
            ·
              refine ⟨76072571269548442230904181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50715047513032294820602787 76072571269548442230904181)
              ·
                refine ⟨7131803556520166459147267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76072571269548442230904181 7131803556520166459147267)
                ·
                  refine ⟨10697705334780249688720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131803556520166459147267 10697705334780249688720901)
                  ·
                    refine ⟨2005819750271296816635169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10697705334780249688720901 2005819750271296816635169)
                    ·
                      refine ⟨1504364812703472612476377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005819750271296816635169 1504364812703472612476377)
                      ·
                        rfl

theorem cell23_2929740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_2929740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929740 prefixEnd_2929740 := by exact prefixLift 2929740
  have htrace : WordTrace (prefixWord ++ tailWord_2929740) baseStart_2929740 baseEnd_2929740 := by
    simpa [prefixWord, tailWord_2929740, baseEnd_2929740] using wordTrace_append hprefix tailTrace_2929740
  have hstable : (prefixWord ++ tailWord_2929740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929740).length < 2 ^ (prefixWord ++ tailWord_2929740).sum := by decide
  have hdescent : baseEnd_2929740 < baseStart_2929740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929774 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2929774 : Nat := 118140960795 + 2929774 * 2 ^ 59
def prefixEnd_2929774 : Nat := 4983230072969 + 3 ^ 40 * 2929774 * 2
def baseEnd_2929774 : Nat := 1504382271045725479451221

theorem tailTrace_2929774 : CollatzResearch.WordTrace tailWord_2929774 prefixEnd_2929774 1504382271045725479451221 := by
  unfold tailWord_2929774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357204560992079801021547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71238424325291092272114917 13357204560992079801021547)
  ·
    refine ⟨20035806841488119701532321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13357204560992079801021547 20035806841488119701532321)
    ·
      refine ⟨15026855131116089776149241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20035806841488119701532321 15026855131116089776149241)
      ·
        refine ⟨11270141348337067332111931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15026855131116089776149241 11270141348337067332111931)
        ·
          refine ⟨16905212022505600998167897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11270141348337067332111931 16905212022505600998167897)
          ·
            refine ⟨12678909016879200748625923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16905212022505600998167897 12678909016879200748625923)
            ·
              refine ⟨19018363525318801122938885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12678909016879200748625923 19018363525318801122938885)
              ·
                refine ⟨3565943160997275210551041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19018363525318801122938885 3565943160997275210551041)
                ·
                  refine ⟨2674457370747956407913281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3565943160997275210551041 2674457370747956407913281)
                  ·
                    refine ⟨2005843028060967305934961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674457370747956407913281 2005843028060967305934961)
                    ·
                      refine ⟨1504382271045725479451221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005843028060967305934961 1504382271045725479451221)
                      ·
                        rfl

theorem cell23_2929774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2929774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929774 prefixEnd_2929774 := by exact prefixLift 2929774
  have htrace : WordTrace (prefixWord ++ tailWord_2929774) baseStart_2929774 baseEnd_2929774 := by
    simpa [prefixWord, tailWord_2929774, baseEnd_2929774] using wordTrace_append hprefix tailTrace_2929774
  have hstable : (prefixWord ++ tailWord_2929774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929774).length < 2 ^ (prefixWord ++ tailWord_2929774).sum := by decide
  have hdescent : baseEnd_2929774 < baseStart_2929774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929810 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_2929810 : Nat := 118140960795 + 2929810 * 2 ^ 59
def prefixEnd_2929810 : Nat := 4983230072969 + 3 ^ 40 * 2929810 * 2
def baseEnd_2929810 : Nat := 501466918783095779533685

theorem tailTrace_2929810 : CollatzResearch.WordTrace tailWord_2929810 prefixEnd_2929810 501466918783095779533685 := by
  unfold tailWord_2929810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714737378951554139120721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71239299677204144370988589 26714737378951554139120721)
  ·
    refine ⟨20036053034213665604340541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26714737378951554139120721 20036053034213665604340541)
    ·
      refine ⟨7513519887830124601627703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20036053034213665604340541 7513519887830124601627703)
      ·
        refine ⟨11270279831745186902441555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513519887830124601627703 11270279831745186902441555)
        ·
          refine ⟨16905419747617780353662333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11270279831745186902441555 16905419747617780353662333)
          ·
            refine ⟨6339532405356667632623375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16905419747617780353662333 6339532405356667632623375)
            ·
              refine ⟨9509298608035001448935063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6339532405356667632623375 9509298608035001448935063)
              ·
                refine ⟨14263947912052502173402595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9509298608035001448935063 14263947912052502173402595)
                ·
                  refine ⟨21395921868078753260103893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14263947912052502173402595 21395921868078753260103893)
                  ·
                    refine ⟨501466918783095779533685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21395921868078753260103893 501466918783095779533685)
                    ·
                      rfl

theorem cell23_2929810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_2929810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929810 prefixEnd_2929810 := by exact prefixLift 2929810
  have htrace : WordTrace (prefixWord ++ tailWord_2929810) baseStart_2929810 baseEnd_2929810 := by
    simpa [prefixWord, tailWord_2929810, baseEnd_2929810] using wordTrace_append hprefix tailTrace_2929810
  have hstable : (prefixWord ++ tailWord_2929810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929810).length < 2 ^ (prefixWord ++ tailWord_2929810).sum := by decide
  have hdescent : baseEnd_2929810 < baseStart_2929810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_2929833 : Nat := 118140960795 + 2929833 * 2 ^ 59
def prefixEnd_2929833 : Nat := 4983230072969 + 3 ^ 40 * 2929833 * 2
def baseEnd_2929833 : Nat := 1504412566404340748613449

theorem tailTrace_2929833 : CollatzResearch.WordTrace tailWord_2929833 prefixEnd_2929833 1504412566404340748613449 := by
  unfold tailWord_2929833
  simp only [CollatzResearch.WordTrace]
  refine ⟨106859788394722891484570153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71239858929815260989713435 106859788394722891484570153)
  ·
    refine ⟨80144841296042168613427615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106859788394722891484570153 80144841296042168613427615)
    ·
      refine ⟨120217261944063252920141423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80144841296042168613427615 120217261944063252920141423)
      ·
        refine ⟨180325892916094879380212135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120217261944063252920141423 180325892916094879380212135)
        ·
          refine ⟨270488839374142319070318203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180325892916094879380212135 270488839374142319070318203)
          ·
            refine ⟨405733259061213478605477305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270488839374142319070318203 405733259061213478605477305)
            ·
              refine ⟨304299944295910108954107979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405733259061213478605477305 304299944295910108954107979)
              ·
                refine ⟨456449916443865163431161969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304299944295910108954107979 456449916443865163431161969)
                ·
                  refine ⟨342337437332898872573371477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456449916443865163431161969 342337437332898872573371477)
                  ·
                    refine ⟨4011766843744908662969197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 342337437332898872573371477 4011766843744908662969197)
                    ·
                      refine ⟨1504412566404340748613449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4011766843744908662969197 1504412566404340748613449)
                      ·
                        rfl

theorem cell23_2929833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_2929833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929833 prefixEnd_2929833 := by exact prefixLift 2929833
  have htrace : WordTrace (prefixWord ++ tailWord_2929833) baseStart_2929833 baseEnd_2929833 := by
    simpa [prefixWord, tailWord_2929833, baseEnd_2929833] using wordTrace_append hprefix tailTrace_2929833
  have hstable : (prefixWord ++ tailWord_2929833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929833).length < 2 ^ (prefixWord ++ tailWord_2929833).sum := by decide
  have hdescent : baseEnd_2929833 < baseStart_2929833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929924 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2929924 : Nat := 118140960795 + 2929924 * 2 ^ 59
def prefixEnd_2929924 : Nat := 4983230072969 + 3 ^ 40 * 2929924 * 2
def baseEnd_2929924 : Nat := 1504459293143899892575531

theorem tailTrace_2929924 : CollatzResearch.WordTrace tailWord_2929924 prefixEnd_2929924 1504459293143899892575531 := by
  unfold tailWord_2929924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53431553718696607013066413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71242071624928809350755217 53431553718696607013066413)
  ·
    refine ⟨20036832644511227629899905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53431553718696607013066413 20036832644511227629899905)
    ·
      refine ⟨15027624483383420722424929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20036832644511227629899905 15027624483383420722424929)
      ·
        refine ⟨11270718362537565541818697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15027624483383420722424929 11270718362537565541818697)
        ·
          refine ⟨8453038771903174156364023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11270718362537565541818697 8453038771903174156364023)
          ·
            refine ⟨12679558157854761234546035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453038771903174156364023 12679558157854761234546035)
            ·
              refine ⟨19019337236782141851819053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679558157854761234546035 19019337236782141851819053)
              ·
                refine ⟨7132251463793303194432145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19019337236782141851819053 7132251463793303194432145)
                ·
                  refine ⟨5349188597844977395824109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7132251463793303194432145 5349188597844977395824109)
                  ·
                    refine ⟨2005945724191866523434041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5349188597844977395824109 2005945724191866523434041)
                    ·
                      refine ⟨1504459293143899892575531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2005945724191866523434041 1504459293143899892575531)
                      ·
                        rfl

theorem cell23_2929924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2929924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929924 prefixEnd_2929924 := by exact prefixLift 2929924
  have htrace : WordTrace (prefixWord ++ tailWord_2929924) baseStart_2929924 baseEnd_2929924 := by
    simpa [prefixWord, tailWord_2929924, baseEnd_2929924] using wordTrace_append hprefix tailTrace_2929924
  have hstable : (prefixWord ++ tailWord_2929924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929924).length < 2 ^ (prefixWord ++ tailWord_2929924).sum := by decide
  have hdescent : baseEnd_2929924 < baseStart_2929924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929934 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_2929934 : Nat := 118140960795 + 2929934 * 2 ^ 59
def prefixEnd_2929934 : Nat := 4983230072969 + 3 ^ 40 * 2929934 * 2
def baseEnd_2929934 : Nat := 501488142650148284483495

theorem tailTrace_2929934 : CollatzResearch.WordTrace tailWord_2929934 prefixEnd_2929934 501488142650148284483495 := by
  unfold tailWord_2929934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357934020919623216749607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71242314778237990489331237 13357934020919623216749607)
  ·
    refine ⟨20036901031379434825124411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13357934020919623216749607 20036901031379434825124411)
    ·
      refine ⟨30055351547069152237686617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20036901031379434825124411 30055351547069152237686617)
      ·
        refine ⟨22541513660301864178264963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30055351547069152237686617 22541513660301864178264963)
        ·
          refine ⟨33812270490452796267397445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22541513660301864178264963 33812270490452796267397445)
          ·
            refine ⟨6339800716959899300137021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33812270490452796267397445 6339800716959899300137021)
            ·
              refine ⟨2377425268859962237551383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6339800716959899300137021 2377425268859962237551383)
              ·
                refine ⟨3566137903289943356327075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377425268859962237551383 3566137903289943356327075)
                ·
                  refine ⟨5349206854934915034490613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566137903289943356327075 5349206854934915034490613)
                  ·
                    refine ⟨501488142650148284483495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5349206854934915034490613 501488142650148284483495)
                    ·
                      rfl

theorem cell23_2929934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_2929934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929934 prefixEnd_2929934 := by exact prefixLift 2929934
  have htrace : WordTrace (prefixWord ++ tailWord_2929934) baseStart_2929934 baseEnd_2929934 := by
    simpa [prefixWord, tailWord_2929934, baseEnd_2929934] using wordTrace_append hprefix tailTrace_2929934
  have hstable : (prefixWord ++ tailWord_2929934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929934).length < 2 ^ (prefixWord ++ tailWord_2929934).sum := by decide
  have hdescent : baseEnd_2929934 < baseStart_2929934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929957 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2929957 : Nat := 118140960795 + 2929957 * 2 ^ 59
def prefixEnd_2929957 : Nat := 4983230072969 + 3 ^ 40 * 2929957 * 2
def baseEnd_2929957 : Nat := 1504476238005498263462879

theorem tailTrace_2929957 : CollatzResearch.WordTrace tailWord_2929957 prefixEnd_2929957 1504476238005498263462879 := by
  unfold tailWord_2929957
  simp only [CollatzResearch.WordTrace]
  refine ⟨106864311046273660662084125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71242874030849107108056083 106864311046273660662084125)
  ·
    refine ⟨40074116642352622748281547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106864311046273660662084125 40074116642352622748281547)
    ·
      refine ⟨60111174963528934122422321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40074116642352622748281547 60111174963528934122422321)
      ·
        refine ⟨45083381222646700591816741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60111174963528934122422321 45083381222646700591816741)
        ·
          refine ⟨8453133979246256360965639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45083381222646700591816741 8453133979246256360965639)
          ·
            refine ⟨12679700968869384541448459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453133979246256360965639 12679700968869384541448459)
            ·
              refine ⟨19019551453304076812172689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679700968869384541448459 19019551453304076812172689)
              ·
                refine ⟨14264663589978057609129517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19019551453304076812172689 14264663589978057609129517)
                ·
                  refine ⟨5349248846241771603423569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14264663589978057609129517 5349248846241771603423569)
                  ·
                    refine ⟨4011936634681328702567677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5349248846241771603423569 4011936634681328702567677)
                    ·
                      refine ⟨1504476238005498263462879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4011936634681328702567677 1504476238005498263462879)
                      ·
                        rfl

theorem cell23_2929957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2929957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929957 prefixEnd_2929957 := by exact prefixLift 2929957
  have htrace : WordTrace (prefixWord ++ tailWord_2929957) baseStart_2929957 baseEnd_2929957 := by
    simpa [prefixWord, tailWord_2929957, baseEnd_2929957] using wordTrace_append hprefix tailTrace_2929957
  have hstable : (prefixWord ++ tailWord_2929957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929957).length < 2 ^ (prefixWord ++ tailWord_2929957).sum := by decide
  have hdescent : baseEnd_2929957 < baseStart_2929957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929987 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 3]
def baseStart_2929987 : Nat := 118140960795 + 2929987 * 2 ^ 59
def prefixEnd_2929987 : Nat := 4983230072969 + 3 ^ 40 * 2929987 * 2
def baseEnd_2929987 : Nat := 1504491642425133146087741

theorem tailTrace_2929987 : CollatzResearch.WordTrace tailWord_2929987 prefixEnd_2929987 1504491642425133146087741 := by
  unfold tailWord_2929987
  simp only [CollatzResearch.WordTrace]
  refine ⟨106865405236164975785676215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71243603490776650523784143 106865405236164975785676215)
  ·
    refine ⟨160298107854247463678514323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106865405236164975785676215 160298107854247463678514323)
    ·
      refine ⟨240447161781371195517771485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160298107854247463678514323 240447161781371195517771485)
      ·
        refine ⟨90167685668014198319164307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240447161781371195517771485 90167685668014198319164307)
        ·
          refine ⟨135251528502021297478746461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90167685668014198319164307 135251528502021297478746461)
          ·
            refine ⟨50719323188257986554529923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135251528502021297478746461 50719323188257986554529923)
            ·
              refine ⟨76078984782386979831794885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50719323188257986554529923 76078984782386979831794885)
              ·
                refine ⟨14264809646697558718461541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76078984782386979831794885 14264809646697558718461541)
                ·
                  refine ⟨2674651808755792259711539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14264809646697558718461541 2674651808755792259711539)
                  ·
                    refine ⟨4011977713133688389567309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2674651808755792259711539 4011977713133688389567309)
                    ·
                      refine ⟨1504491642425133146087741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4011977713133688389567309 1504491642425133146087741)
                      ·
                        rfl

theorem cell23_2929987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_2929987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929987 prefixEnd_2929987 := by exact prefixLift 2929987
  have htrace : WordTrace (prefixWord ++ tailWord_2929987) baseStart_2929987 baseEnd_2929987 := by
    simpa [prefixWord, tailWord_2929987, baseEnd_2929987] using wordTrace_append hprefix tailTrace_2929987
  have hstable : (prefixWord ++ tailWord_2929987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929987).length < 2 ^ (prefixWord ++ tailWord_2929987).sum := by decide
  have hdescent : baseEnd_2929987 < baseStart_2929987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929988 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2929988 : Nat := 118140960795 + 2929988 * 2 ^ 59
def prefixEnd_2929988 : Nat := 4983230072969 + 3 ^ 40 * 2929988 * 2
def baseEnd_2929988 : Nat := 1504492155905787642175237

theorem tailTrace_2929988 : CollatzResearch.WordTrace tailWord_2929988 prefixEnd_2929988 1504492155905787642175237 := by
  unfold tailWord_2929988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53432720854580676478231309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71243627806107568637641745 53432720854580676478231309)
  ·
    refine ⟨20037270320467753679336741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53432720854580676478231309 20037270320467753679336741)
    ·
      refine ⟨3756988185087703814875639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20037270320467753679336741 3756988185087703814875639)
      ·
        refine ⟨5635482277631555722313459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756988185087703814875639 5635482277631555722313459)
        ·
          refine ⟨8453223416447333583470189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635482277631555722313459 8453223416447333583470189)
          ·
            refine ⟨3169958781167750093801321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8453223416447333583470189 3169958781167750093801321)
            ·
              refine ⟨2377469085875812570350991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169958781167750093801321 2377469085875812570350991)
              ·
                refine ⟨3566203628813718855526487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377469085875812570350991 3566203628813718855526487)
                ·
                  refine ⟨5349305443220578283289731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566203628813718855526487 5349305443220578283289731)
                  ·
                    refine ⟨8023958164830867424934597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349305443220578283289731 8023958164830867424934597)
                    ·
                      refine ⟨1504492155905787642175237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8023958164830867424934597 1504492155905787642175237)
                      ·
                        rfl

theorem cell23_2929988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2929988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929988 prefixEnd_2929988 := by exact prefixLift 2929988
  have htrace : WordTrace (prefixWord ++ tailWord_2929988) baseStart_2929988 baseEnd_2929988 := by
    simpa [prefixWord, tailWord_2929988, baseEnd_2929988] using wordTrace_append hprefix tailTrace_2929988
  have hstable : (prefixWord ++ tailWord_2929988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929988).length < 2 ^ (prefixWord ++ tailWord_2929988).sum := by decide
  have hdescent : baseEnd_2929988 < baseStart_2929988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2929991 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_2929991 : Nat := 118140960795 + 2929991 * 2 ^ 59
def prefixEnd_2929991 : Nat := 4983230072969 + 3 ^ 40 * 2929991 * 2
def baseEnd_2929991 : Nat := 1504493696347751130437723

theorem tailTrace_2929991 : CollatzResearch.WordTrace tailWord_2929991 prefixEnd_2929991 1504493696347751130437723 := by
  unfold tailWord_2929991
  simp only [CollatzResearch.WordTrace]
  refine ⟨106865551128150484468821827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71243700752100322979214551 106865551128150484468821827)
  ·
    refine ⟨160298326692225726703232741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106865551128150484468821827 160298326692225726703232741)
    ·
      refine ⟨30055936254792323756856139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160298326692225726703232741 30055936254792323756856139)
      ·
        refine ⟨45083904382188485635284209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30055936254792323756856139 45083904382188485635284209)
        ·
          refine ⟨33812928286641364226463157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45083904382188485635284209 33812928286641364226463157)
          ·
            refine ⟨3169962026872627896230921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33812928286641364226463157 3169962026872627896230921)
            ·
              refine ⟨2377471520154470922173191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3169962026872627896230921 2377471520154470922173191)
              ·
                refine ⟨3566207280231706383259787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377471520154470922173191 3566207280231706383259787)
                ·
                  refine ⟨5349310920347559574889681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566207280231706383259787 5349310920347559574889681)
                  ·
                    refine ⟨4011983190260669681167261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5349310920347559574889681 4011983190260669681167261)
                    ·
                      refine ⟨1504493696347751130437723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4011983190260669681167261 1504493696347751130437723)
                      ·
                        rfl

theorem cell23_2929991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_2929991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2929991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2929991 prefixEnd_2929991 := by exact prefixLift 2929991
  have htrace : WordTrace (prefixWord ++ tailWord_2929991) baseStart_2929991 baseEnd_2929991 := by
    simpa [prefixWord, tailWord_2929991, baseEnd_2929991] using wordTrace_append hprefix tailTrace_2929991
  have hstable : (prefixWord ++ tailWord_2929991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2929991).length < 2 ^ (prefixWord ++ tailWord_2929991).sum := by decide
  have hdescent : baseEnd_2929991 < baseStart_2929991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2929991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930004 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2930004 : Nat := 118140960795 + 2930004 * 2 ^ 59
def prefixEnd_2930004 : Nat := 4983230072969 + 3 ^ 40 * 2930004 * 2
def baseEnd_2930004 : Nat := 1504500371596259579575163

theorem tailTrace_2930004 : CollatzResearch.WordTrace tailWord_2930004 prefixEnd_2930004 1504500371596259579575163 := by
  unfold tailWord_2930004
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433012638551693844522533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71244016851402258459363377 53433012638551693844522533)
  ·
    refine ⟨10018689869728442595847975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53433012638551693844522533 10018689869728442595847975)
    ·
      refine ⟨15028034804592663893771963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018689869728442595847975 15028034804592663893771963)
      ·
        refine ⟨22542052206888995840657945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028034804592663893771963 22542052206888995840657945)
        ·
          refine ⟨16906539155166746880493459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22542052206888995840657945 16906539155166746880493459)
          ·
            refine ⟨25359808732750120320740189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16906539155166746880493459 25359808732750120320740189)
            ·
              refine ⟨9509928274781295120277571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25359808732750120320740189 9509928274781295120277571)
              ·
                refine ⟨14264892412171942680416357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9509928274781295120277571 14264892412171942680416357)
                ·
                  refine ⟨2674667327282239252578067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14264892412171942680416357 2674667327282239252578067)
                  ·
                    refine ⟨4012000990923358878867101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2674667327282239252578067 4012000990923358878867101)
                    ·
                      refine ⟨1504500371596259579575163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012000990923358878867101 1504500371596259579575163)
                      ·
                        rfl

theorem cell23_2930004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2930004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930004 prefixEnd_2930004 := by exact prefixLift 2930004
  have htrace : WordTrace (prefixWord ++ tailWord_2930004) baseStart_2930004 baseEnd_2930004 := by
    simpa [prefixWord, tailWord_2930004, baseEnd_2930004] using wordTrace_append hprefix tailTrace_2930004
  have hstable : (prefixWord ++ tailWord_2930004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930004).length < 2 ^ (prefixWord ++ tailWord_2930004).sum := by decide
  have hdescent : baseEnd_2930004 < baseStart_2930004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930010 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2930010 : Nat := 118140960795 + 2930010 * 2 ^ 59
def prefixEnd_2930010 : Nat := 4983230072969 + 3 ^ 40 * 2930010 * 2
def baseEnd_2930010 : Nat := 1504503452480186556100135

theorem tailTrace_2930010 : CollatzResearch.WordTrace tailWord_2930010 prefixEnd_2930010 1504503452480186556100135 := by
  unfold tailWord_2930010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26716561028770412678440871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71244162743387767142508989 26716561028770412678440871)
  ·
    refine ⟨40074841543155619017661307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26716561028770412678440871 40074841543155619017661307)
    ·
      refine ⟨60112262314733428526491961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40074841543155619017661307 60112262314733428526491961)
      ·
        refine ⟨45084196736050071394868971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60112262314733428526491961 45084196736050071394868971)
        ·
          refine ⟨67626295104075107092303457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45084196736050071394868971 67626295104075107092303457)
          ·
            refine ⟨50719721328056330319227593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67626295104075107092303457 50719721328056330319227593)
            ·
              refine ⟨38039790996042247739420695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50719721328056330319227593 38039790996042247739420695)
              ·
                refine ⟨57059686494063371609131043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38039790996042247739420695 57059686494063371609131043)
                ·
                  refine ⟨85589529741095057413696565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57059686494063371609131043 85589529741095057413696565)
                  ·
                    refine ⟨8024018413227661632534053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85589529741095057413696565 8024018413227661632534053)
                    ·
                      refine ⟨1504503452480186556100135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8024018413227661632534053 1504503452480186556100135)
                      ·
                        rfl

theorem cell23_2930010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2930010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930010 prefixEnd_2930010 := by exact prefixLift 2930010
  have htrace : WordTrace (prefixWord ++ tailWord_2930010) baseStart_2930010 baseEnd_2930010 := by
    simpa [prefixWord, tailWord_2930010, baseEnd_2930010] using wordTrace_append hprefix tailTrace_2930010
  have hstable : (prefixWord ++ tailWord_2930010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930010).length < 2 ^ (prefixWord ++ tailWord_2930010).sum := by decide
  have hdescent : baseEnd_2930010 < baseStart_2930010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930021 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_2930021 : Nat := 118140960795 + 2930021 * 2 ^ 59
def prefixEnd_2930021 : Nat := 4983230072969 + 3 ^ 40 * 2930021 * 2
def baseEnd_2930021 : Nat := 1504509100767386013062585

theorem tailTrace_2930021 : CollatzResearch.WordTrace tailWord_2930021 prefixEnd_2930021 1504509100767386013062585 := by
  unfold tailWord_2930021
  simp only [CollatzResearch.WordTrace]
  refine ⟨106866645318041799592413917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71244430212027866394942611 106866645318041799592413917)
  ·
    refine ⟨40074991994265674847155219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106866645318041799592413917 40074991994265674847155219)
    ·
      refine ⟨60112487991398512270732829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40074991994265674847155219 60112487991398512270732829)
      ·
        refine ⟨22542182996774442101524811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60112487991398512270732829 22542182996774442101524811)
        ·
          refine ⟨33813274495161663152287217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22542182996774442101524811 33813274495161663152287217)
          ·
            refine ⟨25359955871371247364215413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33813274495161663152287217 25359955871371247364215413)
            ·
              refine ⟨2377495862941054440395195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25359955871371247364215413 2377495862941054440395195)
              ·
                refine ⟨3566243794411581660592793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2377495862941054440395195 3566243794411581660592793)
                ·
                  refine ⟨2674682845808686245444595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3566243794411581660592793 2674682845808686245444595)
                  ·
                    refine ⟨4012024268713029368166893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2674682845808686245444595 4012024268713029368166893)
                    ·
                      refine ⟨1504509100767386013062585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012024268713029368166893 1504509100767386013062585)
                      ·
                        rfl

theorem cell23_2930021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_2930021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930021 prefixEnd_2930021 := by exact prefixLift 2930021
  have htrace : WordTrace (prefixWord ++ tailWord_2930021) baseStart_2930021 baseEnd_2930021 := by
    simpa [prefixWord, tailWord_2930021, baseEnd_2930021] using wordTrace_append hprefix tailTrace_2930021
  have hstable : (prefixWord ++ tailWord_2930021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930021).length < 2 ^ (prefixWord ++ tailWord_2930021).sum := by decide
  have hdescent : baseEnd_2930021 < baseStart_2930021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930044 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_2930044 : Nat := 118140960795 + 2930044 * 2 ^ 59
def prefixEnd_2930044 : Nat := 4983230072969 + 3 ^ 40 * 2930044 * 2
def baseEnd_2930044 : Nat := 1504520910822439423074979

theorem tailTrace_2930044 : CollatzResearch.WordTrace tailWord_2930044 prefixEnd_2930044 1504520910822439423074979 := by
  unfold tailWord_2930044
  simp only [CollatzResearch.WordTrace]
  refine ⟨53433742098479237260250593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71244989464638983013667457 53433742098479237260250593)
  ·
    refine ⟨40075306573859427945187945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53433742098479237260250593 40075306573859427945187945)
    ·
      refine ⟨30056479930394570958890959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40075306573859427945187945 30056479930394570958890959)
      ·
        refine ⟨45084719895591856438336439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30056479930394570958890959 45084719895591856438336439)
        ·
          refine ⟨67627079843387784657504659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45084719895591856438336439 67627079843387784657504659)
          ·
            refine ⟨101440619765081676986256989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67627079843387784657504659 101440619765081676986256989)
            ·
              refine ⟨38040232411905628869846371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101440619765081676986256989 38040232411905628869846371)
              ·
                refine ⟨57060348617858443304769557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38040232411905628869846371 57060348617858443304769557)
                ·
                  refine ⟨2674703841462114529911073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57060348617858443304769557 2674703841462114529911073)
                  ·
                    refine ⟨2006027881096585897433305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2674703841462114529911073 2006027881096585897433305)
                    ·
                      refine ⟨1504520910822439423074979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006027881096585897433305 1504520910822439423074979)
                      ·
                        rfl

theorem cell23_2930044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_2930044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930044 prefixEnd_2930044 := by exact prefixLift 2930044
  have htrace : WordTrace (prefixWord ++ tailWord_2930044) baseStart_2930044 baseEnd_2930044 := by
    simpa [prefixWord, tailWord_2930044, baseEnd_2930044] using wordTrace_append hprefix tailTrace_2930044
  have hstable : (prefixWord ++ tailWord_2930044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930044).length < 2 ^ (prefixWord ++ tailWord_2930044).sum := by decide
  have hdescent : baseEnd_2930044 < baseStart_2930044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930060 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2930060 : Nat := 118140960795 + 2930060 * 2 ^ 59
def prefixEnd_2930060 : Nat := 4983230072969 + 3 ^ 40 * 2930060 * 2
def baseEnd_2930060 : Nat := 1504529126512911360474905

theorem tailTrace_2930060 : CollatzResearch.WordTrace tailWord_2930060 prefixEnd_2930060 1504529126512911360474905 := by
  unfold tailWord_2930060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53434033882450254626541817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71245378509933672835389089 53434033882450254626541817)
  ·
    refine ⟨40075525411837690969906363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53434033882450254626541817 40075525411837690969906363)
    ·
      refine ⟨60113288117756536454859545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40075525411837690969906363 60113288117756536454859545)
      ·
        refine ⟨45084966088317402341144659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60113288117756536454859545 45084966088317402341144659)
        ·
          refine ⟨67627449132476103511716989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45084966088317402341144659 67627449132476103511716989)
          ·
            refine ⟨25360293424678538816893871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67627449132476103511716989 25360293424678538816893871)
            ·
              refine ⟨38040440137017808225340807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25360293424678538816893871 38040440137017808225340807)
              ·
                refine ⟨57060660205526712338011211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38040440137017808225340807 57060660205526712338011211)
                ·
                  refine ⟨85590990308290068507016817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57060660205526712338011211 85590990308290068507016817)
                  ·
                    refine ⟨64193242731217551380262613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85590990308290068507016817 64193242731217551380262613)
                    ·
                      refine ⟨1504529126512911360474905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64193242731217551380262613 1504529126512911360474905)
                      ·
                        rfl

theorem cell23_2930060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2930060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930060 prefixEnd_2930060 := by exact prefixLift 2930060
  have htrace : WordTrace (prefixWord ++ tailWord_2930060) baseStart_2930060 baseEnd_2930060 := by
    simpa [prefixWord, tailWord_2930060, baseEnd_2930060] using wordTrace_append hprefix tailTrace_2930060
  have hstable : (prefixWord ++ tailWord_2930060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930060).length < 2 ^ (prefixWord ++ tailWord_2930060).sum := by decide
  have hdescent : baseEnd_2930060 < baseStart_2930060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930151 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2930151 : Nat := 118140960795 + 2930151 * 2 ^ 59
def prefixEnd_2930151 : Nat := 4983230072969 + 3 ^ 40 * 2930151 * 2
def baseEnd_2930151 : Nat := 1504575853252470504436987

theorem tailTrace_2930151 : CollatzResearch.WordTrace tailWord_2930151 prefixEnd_2930151 1504575853252470504436987 := by
  unfold tailWord_2930151
  simp only [CollatzResearch.WordTrace]
  refine ⟨106871386807570831794646307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71247591205047221196430871 106871386807570831794646307)
  ·
    refine ⟨160307080211356247691969461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106871386807570831794646307 160307080211356247691969461)
    ·
      refine ⟨15028788769814648221122137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160307080211356247691969461 15028788769814648221122137)
      ·
        refine ⟨11271591577360986165841603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15028788769814648221122137 11271591577360986165841603)
        ·
          refine ⟨16907387366041479248762405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271591577360986165841603 16907387366041479248762405)
          ·
            refine ⟨3170135131132777359142951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16907387366041479248762405 3170135131132777359142951)
            ·
              refine ⟨4755202696699166038714427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170135131132777359142951 4755202696699166038714427)
              ·
                refine ⟨7132804045048749058071641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755202696699166038714427 7132804045048749058071641)
                ·
                  refine ⟨5349603033786561793553731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7132804045048749058071641 5349603033786561793553731)
                  ·
                    refine ⟨8024404550679842690330597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349603033786561793553731 8024404550679842690330597)
                    ·
                      refine ⟨1504575853252470504436987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8024404550679842690330597 1504575853252470504436987)
                      ·
                        rfl

theorem cell23_2930151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2930151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930151 prefixEnd_2930151 := by exact prefixLift 2930151
  have htrace : WordTrace (prefixWord ++ tailWord_2930151) baseStart_2930151 baseEnd_2930151 := by
    simpa [prefixWord, tailWord_2930151, baseEnd_2930151] using wordTrace_append hprefix tailTrace_2930151
  have hstable : (prefixWord ++ tailWord_2930151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930151).length < 2 ^ (prefixWord ++ tailWord_2930151).sum := by decide
  have hdescent : baseEnd_2930151 < baseStart_2930151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930161 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 1, 4]
def baseStart_2930161 : Nat := 118140960795 + 2930161 * 2 ^ 59
def prefixEnd_2930161 : Nat := 4983230072969 + 3 ^ 40 * 2930161 * 2
def baseEnd_2930161 : Nat := 501526996019671821770647

theorem tailTrace_2930161 : CollatzResearch.WordTrace tailWord_2930161 prefixEnd_2930161 501526996019671821770647 := by
  unfold tailWord_2930161
  simp only [CollatzResearch.WordTrace]
  refine ⟨106871751537534603502510337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71247834358356402335006891 106871751537534603502510337)
  ·
    refine ⟨80153813653150952626882753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106871751537534603502510337 80153813653150952626882753)
    ·
      refine ⟨60115360239863214470162065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80153813653150952626882753 60115360239863214470162065)
      ·
        refine ⟨45086520179897410852621549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60115360239863214470162065 45086520179897410852621549)
        ·
          refine ⟨16907445067461529069733081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45086520179897410852621549 16907445067461529069733081)
          ·
            refine ⟨12680583800596146802299811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16907445067461529069733081 12680583800596146802299811)
            ·
              refine ⟨19020875700894220203449717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12680583800596146802299811 19020875700894220203449717)
              ·
                refine ⟨1783207096958833144073411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19020875700894220203449717 1783207096958833144073411)
                ·
                  refine ⟨2674810645438249716110117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783207096958833144073411 2674810645438249716110117)
                  ·
                    refine ⟨501526996019671821770647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674810645438249716110117 501526996019671821770647)
                    ·
                      rfl

theorem cell23_2930161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_2930161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930161 prefixEnd_2930161 := by exact prefixLift 2930161
  have htrace : WordTrace (prefixWord ++ tailWord_2930161) baseStart_2930161 baseEnd_2930161 := by
    simpa [prefixWord, tailWord_2930161, baseEnd_2930161] using wordTrace_append hprefix tailTrace_2930161
  have hstable : (prefixWord ++ tailWord_2930161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930161).length < 2 ^ (prefixWord ++ tailWord_2930161).sum := by decide
  have hdescent : baseEnd_2930161 < baseStart_2930161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930178 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2930178 : Nat := 118140960795 + 2930178 * 2 ^ 59
def prefixEnd_2930178 : Nat := 4983230072969 + 3 ^ 40 * 2930178 * 2
def baseEnd_2930178 : Nat := 501529905743380632933121

theorem tailTrace_2930178 : CollatzResearch.WordTrace tailWord_2930178 prefixEnd_2930178 501529905743380632933121 := by
  unfold tailWord_2930178
  simp only [CollatzResearch.WordTrace]
  refine ⟨26718092894618253851469797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71248247718982010270586125 26718092894618253851469797)
  ·
    refine ⟨5009642417740922597150587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26718092894618253851469797 5009642417740922597150587)
    ·
      refine ⟨7514463626611383895725881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009642417740922597150587 7514463626611383895725881)
      ·
        refine ⟨5635847719958537921794411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7514463626611383895725881 5635847719958537921794411)
        ·
          refine ⟨8453771579937806882691617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635847719958537921794411 8453771579937806882691617)
          ·
            refine ⟨6340328684953355162018713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8453771579937806882691617 6340328684953355162018713)
            ·
              refine ⟨4755246513715016371514035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340328684953355162018713 4755246513715016371514035)
              ·
                refine ⟨7132869770572524557271053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755246513715016371514035 7132869770572524557271053)
                ·
                  refine ⟨2674826163964696708976645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7132869770572524557271053 2674826163964696708976645)
                  ·
                    refine ⟨501529905743380632933121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674826163964696708976645 501529905743380632933121)
                    ·
                      rfl

theorem cell23_2930178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2930178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930178 prefixEnd_2930178 := by exact prefixLift 2930178
  have htrace : WordTrace (prefixWord ++ tailWord_2930178) baseStart_2930178 baseEnd_2930178 := by
    simpa [prefixWord, tailWord_2930178, baseEnd_2930178] using wordTrace_append hprefix tailTrace_2930178
  have hstable : (prefixWord ++ tailWord_2930178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930178).length < 2 ^ (prefixWord ++ tailWord_2930178).sum := by decide
  have hdescent : baseEnd_2930178 < baseStart_2930178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930234 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_2930234 : Nat := 118140960795 + 2930234 * 2 ^ 59
def prefixEnd_2930234 : Nat := 4983230072969 + 3 ^ 40 * 2930234 * 2
def baseEnd_2930234 : Nat := 501539490715597893233035

theorem tailTrace_2930234 : CollatzResearch.WordTrace tailWord_2930234 prefixEnd_2930234 501539490715597893233035 := by
  unfold tailWord_2930234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26718603516567534242479439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71249609377513424646611837 26718603516567534242479439)
  ·
    refine ⟨40077905274851301363719159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26718603516567534242479439 40077905274851301363719159)
    ·
      refine ⟨60116857912276952045578739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40077905274851301363719159 60116857912276952045578739)
      ·
        refine ⟨90175286868415428068368109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60116857912276952045578739 90175286868415428068368109)
        ·
          refine ⟨33815732575655785525638041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90175286868415428068368109 33815732575655785525638041)
          ·
            refine ⟨25361799431741839144228531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33815732575655785525638041 25361799431741839144228531)
            ·
              refine ⟨38042699147612758716342797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25361799431741839144228531 38042699147612758716342797)
              ·
                refine ⟨14266012180354784518628549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38042699147612758716342797 14266012180354784518628549)
                ·
                  refine ⟨2674877283816522097242853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14266012180354784518628549 2674877283816522097242853)
                  ·
                    refine ⟨501539490715597893233035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674877283816522097242853 501539490715597893233035)
                    ·
                      rfl

theorem cell23_2930234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_2930234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930234 prefixEnd_2930234 := by exact prefixLift 2930234
  have htrace : WordTrace (prefixWord ++ tailWord_2930234) baseStart_2930234 baseEnd_2930234 := by
    simpa [prefixWord, tailWord_2930234, baseEnd_2930234] using wordTrace_append hprefix tailTrace_2930234
  have hstable : (prefixWord ++ tailWord_2930234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930234).length < 2 ^ (prefixWord ++ tailWord_2930234).sum := by decide
  have hdescent : baseEnd_2930234 < baseStart_2930234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930254 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2930254 : Nat := 118140960795 + 2930254 * 2 ^ 59
def prefixEnd_2930254 : Nat := 4983230072969 + 3 ^ 40 * 2930254 * 2
def baseEnd_2930254 : Nat := 1504628741759883601449013

theorem tailTrace_2930254 : CollatzResearch.WordTrace tailWord_2930254 prefixEnd_2930254 1504628741759883601449013 := by
  unfold tailWord_2930254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359392940774710048205727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71250095684131786923763877 13359392940774710048205727)
  ·
    refine ⟨20039089411162065072308591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359392940774710048205727 20039089411162065072308591)
    ·
      refine ⟨30058634116743097608462887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20039089411162065072308591 30058634116743097608462887)
      ·
        refine ⟨45087951175114646412694331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30058634116743097608462887 45087951175114646412694331)
        ·
          refine ⟨67631926762671969619041497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45087951175114646412694331 67631926762671969619041497)
          ·
            refine ⟨50723945072003977214281123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67631926762671969619041497 50723945072003977214281123)
            ·
              refine ⟨76085917608005965821421685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50723945072003977214281123 76085917608005965821421685)
              ·
                refine ⟨7133054775750559295758283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76085917608005965821421685 7133054775750559295758283)
                ·
                  refine ⟨10699582163625838943637425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133054775750559295758283 10699582163625838943637425)
                  ·
                    refine ⟨8024686622719379207728069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10699582163625838943637425 8024686622719379207728069)
                    ·
                      refine ⟨1504628741759883601449013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8024686622719379207728069 1504628741759883601449013)
                      ·
                        rfl

theorem cell23_2930254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2930254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930254 prefixEnd_2930254 := by exact prefixLift 2930254
  have htrace : WordTrace (prefixWord ++ tailWord_2930254) baseStart_2930254 baseEnd_2930254 := by
    simpa [prefixWord, tailWord_2930254, baseEnd_2930254] using wordTrace_append hprefix tailTrace_2930254
  have hstable : (prefixWord ++ tailWord_2930254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930254).length < 2 ^ (prefixWord ++ tailWord_2930254).sum := by decide
  have hdescent : baseEnd_2930254 < baseStart_2930254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930258 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2930258 : Nat := 118140960795 + 2930258 * 2 ^ 59
def prefixEnd_2930258 : Nat := 4983230072969 + 3 ^ 40 * 2930258 * 2
def baseEnd_2930258 : Nat := 1504630795682501585798995

theorem tailTrace_2930258 : CollatzResearch.WordTrace tailWord_2930258 prefixEnd_2930258 1504630795682501585798995 := by
  unfold tailWord_2930258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26718822354545797267197857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71250192945455459379194285 26718822354545797267197857)
  ·
    refine ⟨20039116765909347950398393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26718822354545797267197857 20039116765909347950398393)
    ·
      refine ⟨15029337574432010962798795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20039116765909347950398393 15029337574432010962798795)
      ·
        refine ⟨22544006361648016444198193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15029337574432010962798795 22544006361648016444198193)
        ·
          refine ⟨16908004771236012333148645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22544006361648016444198193 16908004771236012333148645)
          ·
            refine ⟨3170250894606752312465371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16908004771236012333148645 3170250894606752312465371)
            ·
              refine ⟨4755376341910128468698057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170250894606752312465371 4755376341910128468698057)
              ·
                refine ⟨3566532256432596351523543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755376341910128468698057 3566532256432596351523543)
                ·
                  refine ⟨5349798384648894527285315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566532256432596351523543 5349798384648894527285315)
                  ·
                    refine ⟨8024697576973341790927973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349798384648894527285315 8024697576973341790927973)
                    ·
                      refine ⟨1504630795682501585798995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8024697576973341790927973 1504630795682501585798995)
                      ·
                        rfl

theorem cell23_2930258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2930258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930258 prefixEnd_2930258 := by exact prefixLift 2930258
  have htrace : WordTrace (prefixWord ++ tailWord_2930258) baseStart_2930258 baseEnd_2930258 := by
    simpa [prefixWord, tailWord_2930258, baseEnd_2930258] using wordTrace_append hprefix tailTrace_2930258
  have hstable : (prefixWord ++ tailWord_2930258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930258).length < 2 ^ (prefixWord ++ tailWord_2930258).sum := by decide
  have hdescent : baseEnd_2930258 < baseStart_2930258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930308 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2930308 : Nat := 118140960795 + 2930308 * 2 ^ 59
def prefixEnd_2930308 : Nat := 4983230072969 + 3 ^ 40 * 2930308 * 2
def baseEnd_2930308 : Nat := 1504656469715226390173765

theorem tailTrace_2930308 : CollatzResearch.WordTrace tailWord_2930308 prefixEnd_2930308 1504656469715226390173765 := by
  unfold tailWord_2930308
  simp only [CollatzResearch.WordTrace]
  refine ⟨53438556534001023804055789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71251408712001365072074385 53438556534001023804055789)
  ·
    refine ⟨20039458700250383926520921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53438556534001023804055789 20039458700250383926520921)
    ·
      refine ⟨15029594025187787944890691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20039458700250383926520921 15029594025187787944890691)
      ·
        refine ⟨22544391037781681917336037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15029594025187787944890691 22544391037781681917336037)
        ·
          refine ⟨4227073319584065359500507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22544391037781681917336037 4227073319584065359500507)
          ·
            refine ⟨6340609979376098039250761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227073319584065359500507 6340609979376098039250761)
            ·
              refine ⟨4755457484532073529438071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340609979376098039250761 4755457484532073529438071)
              ·
                refine ⟨7133186226798110294157107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755457484532073529438071 7133186226798110294157107)
                ·
                  refine ⟨10699779340197165441235661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133186226798110294157107 10699779340197165441235661)
                  ·
                    refine ⟨4012417252573937040463373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10699779340197165441235661 4012417252573937040463373)
                    ·
                      refine ⟨1504656469715226390173765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012417252573937040463373 1504656469715226390173765)
                      ·
                        rfl

theorem cell23_2930308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2930308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930308 prefixEnd_2930308 := by exact prefixLift 2930308
  have htrace : WordTrace (prefixWord ++ tailWord_2930308) baseStart_2930308 baseEnd_2930308 := by
    simpa [prefixWord, tailWord_2930308, baseEnd_2930308] using wordTrace_append hprefix tailTrace_2930308
  have hstable : (prefixWord ++ tailWord_2930308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930308).length < 2 ^ (prefixWord ++ tailWord_2930308).sum := by decide
  have hdescent : baseEnd_2930308 < baseStart_2930308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930318 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2930318 : Nat := 118140960795 + 2930318 * 2 ^ 59
def prefixEnd_2930318 : Nat := 4983230072969 + 3 ^ 40 * 2930318 * 2
def baseEnd_2930318 : Nat := 1504661604521771351048719

theorem tailTrace_2930318 : CollatzResearch.WordTrace tailWord_2930318 prefixEnd_2930318 1504661604521771351048719 := by
  unfold tailWord_2930318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359684724745727414496951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71251651865310546210650405 13359684724745727414496951)
  ·
    refine ⟨20039527087118591121745427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359684724745727414496951 20039527087118591121745427)
    ·
      refine ⟨30059290630677886682618141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20039527087118591121745427 30059290630677886682618141)
      ·
        refine ⟨11272233986504207505981803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30059290630677886682618141 11272233986504207505981803)
        ·
          refine ⟨16908350979756311258972705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11272233986504207505981803 16908350979756311258972705)
          ·
            refine ⟨12681263234817233444229529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16908350979756311258972705 12681263234817233444229529)
            ·
              refine ⟨9510947426112925083172147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12681263234817233444229529 9510947426112925083172147)
              ·
                refine ⟨14266421139169387624758221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9510947426112925083172147 14266421139169387624758221)
                ·
                  refine ⟨5349907927188520359284333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14266421139169387624758221 5349907927188520359284333)
                  ·
                    refine ⟨2006215472695695134731625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5349907927188520359284333 2006215472695695134731625)
                    ·
                      refine ⟨1504661604521771351048719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006215472695695134731625 1504661604521771351048719)
                      ·
                        rfl

theorem cell23_2930318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2930318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930318 prefixEnd_2930318 := by exact prefixLift 2930318
  have htrace : WordTrace (prefixWord ++ tailWord_2930318) baseStart_2930318 baseEnd_2930318 := by
    simpa [prefixWord, tailWord_2930318, baseEnd_2930318] using wordTrace_append hprefix tailTrace_2930318
  have hstable : (prefixWord ++ tailWord_2930318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930318).length < 2 ^ (prefixWord ++ tailWord_2930318).sum := by decide
  have hdescent : baseEnd_2930318 < baseStart_2930318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930354 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_2930354 : Nat := 118140960795 + 2930354 * 2 ^ 59
def prefixEnd_2930354 : Nat := 4983230072969 + 3 ^ 40 * 2930354 * 2
def baseEnd_2930354 : Nat := 167186676647259245577617

theorem tailTrace_2930354 : CollatzResearch.WordTrace tailWord_2930354 prefixEnd_2930354 167186676647259245577617 := by
  unfold tailWord_2930354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719697706458849366071529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71252527217223598309524077 26719697706458849366071529)
  ·
    refine ⟨20039773279844137024553647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26719697706458849366071529 20039773279844137024553647)
    ·
      refine ⟨30059659919766205536830471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20039773279844137024553647 30059659919766205536830471)
      ·
        refine ⟨45089489879649308305245707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30059659919766205536830471 45089489879649308305245707)
        ·
          refine ⟨67634234819473962457868561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45089489879649308305245707 67634234819473962457868561)
          ·
            refine ⟨50725676114605471843401421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67634234819473962457868561 50725676114605471843401421)
            ·
              refine ⟨19022128542977051941275533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50725676114605471843401421 19022128542977051941275533)
              ·
                refine ⟨7133298203616394477978325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19022128542977051941275533 7133298203616394477978325)
                ·
                  refine ⟨167186676647259245577617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7133298203616394477978325 167186676647259245577617)
                  ·
                    rfl

theorem cell23_2930354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_2930354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930354 prefixEnd_2930354 := by exact prefixLift 2930354
  have htrace : WordTrace (prefixWord ++ tailWord_2930354) baseStart_2930354 baseEnd_2930354 := by
    simpa [prefixWord, tailWord_2930354, baseEnd_2930354] using wordTrace_append hprefix tailTrace_2930354
  have hstable : (prefixWord ++ tailWord_2930354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930354).length < 2 ^ (prefixWord ++ tailWord_2930354).sum := by decide
  have hdescent : baseEnd_2930354 < baseStart_2930354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930358 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2930358 : Nat := 118140960795 + 2930358 * 2 ^ 59
def prefixEnd_2930358 : Nat := 4983230072969 + 3 ^ 40 * 2930358 * 2
def baseEnd_2930358 : Nat := 501560714582650398182845

theorem tailTrace_2930358 : CollatzResearch.WordTrace tailWord_2930358 prefixEnd_2930358 501560714582650398182845 := by
  unfold tailWord_2930358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679933544863806634214483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71252624478547270764954485 6679933544863806634214483)
  ·
    refine ⟨10019900317295709951321725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679933544863806634214483 10019900317295709951321725)
    ·
      refine ⟨3757462618985891231745647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10019900317295709951321725 3757462618985891231745647)
      ·
        refine ⟨5636193928478836847618471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757462618985891231745647 5636193928478836847618471)
        ·
          refine ⟨8454290892718255271427707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636193928478836847618471 8454290892718255271427707)
          ·
            refine ⟨12681436339077382907141561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454290892718255271427707 12681436339077382907141561)
            ·
              refine ⟨9511077254308037180356171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12681436339077382907141561 9511077254308037180356171)
              ·
                refine ⟨14266615881462055770534257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511077254308037180356171 14266615881462055770534257)
                ·
                  refine ⟨10699961911096541827900693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14266615881462055770534257 10699961911096541827900693)
                  ·
                    refine ⟨501560714582650398182845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10699961911096541827900693 501560714582650398182845)
                    ·
                      rfl

theorem cell23_2930358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2930358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930358 prefixEnd_2930358 := by exact prefixLift 2930358
  have htrace : WordTrace (prefixWord ++ tailWord_2930358) baseStart_2930358 baseEnd_2930358 := by
    simpa [prefixWord, tailWord_2930358, baseEnd_2930358] using wordTrace_append hprefix tailTrace_2930358
  have hstable : (prefixWord ++ tailWord_2930358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930358).length < 2 ^ (prefixWord ++ tailWord_2930358).sum := by decide
  have hdescent : baseEnd_2930358 < baseStart_2930358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930431 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 3, 4]
def baseStart_2930431 : Nat := 118140960795 + 2930431 * 2 ^ 59
def prefixEnd_2930431 : Nat := 4983230072969 + 3 ^ 40 * 2930431 * 2
def baseEnd_2930431 : Nat := 501573209278576469645233

theorem tailTrace_2930431 : CollatzResearch.WordTrace tailWord_2930431 prefixEnd_2930431 501573209278576469645233 := by
  unfold tailWord_2930431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106881599246556439614839147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71254399497704293076559431 106881599246556439614839147)
  ·
    refine ⟨160322398869834659422258721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106881599246556439614839147 160322398869834659422258721)
    ·
      refine ⟨120241799152375994566694041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160322398869834659422258721 120241799152375994566694041)
      ·
        refine ⟨90181349364281995925020531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120241799152375994566694041 90181349364281995925020531)
        ·
          refine ⟨135272024046422993887530797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90181349364281995925020531 135272024046422993887530797)
          ·
            refine ⟨50727009017408622707824049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135272024046422993887530797 50727009017408622707824049)
            ·
              refine ⟨38045256763056467030868037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50727009017408622707824049 38045256763056467030868037)
              ·
                refine ⟨7133485643073087568287757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38045256763056467030868037 7133485643073087568287757)
                ·
                  refine ⟨2675057116152407838107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7133485643073087568287757 2675057116152407838107909)
                  ·
                    refine ⟨501573209278576469645233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675057116152407838107909 501573209278576469645233)
                    ·
                      rfl

theorem cell23_2930431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_2930431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930431 prefixEnd_2930431 := by exact prefixLift 2930431
  have htrace : WordTrace (prefixWord ++ tailWord_2930431) baseStart_2930431 baseEnd_2930431 := by
    simpa [prefixWord, tailWord_2930431, baseEnd_2930431] using wordTrace_append hprefix tailTrace_2930431
  have hstable : (prefixWord ++ tailWord_2930431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930431).length < 2 ^ (prefixWord ++ tailWord_2930431).sum := by decide
  have hdescent : baseEnd_2930431 < baseStart_2930431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930444 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 10]
def baseStart_2930444 : Nat := 118140960795 + 2930444 * 2 ^ 59
def prefixEnd_2930444 : Nat := 4983230072969 + 3 ^ 40 * 2930444 * 2
def baseEnd_2930444 : Nat := 167191811453804206452571

theorem tailTrace_2930444 : CollatzResearch.WordTrace tailWord_2930444 prefixEnd_2930444 167191811453804206452571 := by
  unfold tailWord_2930444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53441036697754671417531193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71254715597006228556708257 53441036697754671417531193)
  ·
    refine ⟨40080777523316003563148395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53441036697754671417531193 40080777523316003563148395)
    ·
      refine ⟨60121166284974005344722593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40080777523316003563148395 60121166284974005344722593)
      ·
        refine ⟨45090874713730504008541945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60121166284974005344722593 45090874713730504008541945)
        ·
          refine ⟨33818156035297878006406459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45090874713730504008541945 33818156035297878006406459)
          ·
            refine ⟨50727234052946817009609689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33818156035297878006406459 50727234052946817009609689)
            ·
              refine ⟨38045425539710112757207267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50727234052946817009609689 38045425539710112757207267)
              ·
                refine ⟨57068138309565169135810901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38045425539710112757207267 57068138309565169135810901)
                ·
                  refine ⟨167191811453804206452571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57068138309565169135810901 167191811453804206452571)
                  ·
                    rfl

theorem cell23_2930444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_2930444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930444 prefixEnd_2930444 := by exact prefixLift 2930444
  have htrace : WordTrace (prefixWord ++ tailWord_2930444) baseStart_2930444 baseEnd_2930444 := by
    simpa [prefixWord, tailWord_2930444, baseEnd_2930444] using wordTrace_append hprefix tailTrace_2930444
  have hstable : (prefixWord ++ tailWord_2930444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930444).length < 2 ^ (prefixWord ++ tailWord_2930444).sum := by decide
  have hdescent : baseEnd_2930444 < baseStart_2930444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930458 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_2930458 : Nat := 118140960795 + 2930458 * 2 ^ 59
def prefixEnd_2930458 : Nat := 4983230072969 + 3 ^ 40 * 2930458 * 2
def baseEnd_2930458 : Nat := 1504733491813400803298075

theorem tailTrace_2930458 : CollatzResearch.WordTrace tailWord_2930458 prefixEnd_2930458 1504733491813400803298075 := by
  unfold tailWord_2930458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26720646004364655806518007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71255056011639082150714685 26720646004364655806518007)
  ·
    refine ⟨40080969006546983709777011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26720646004364655806518007 40080969006546983709777011)
    ·
      refine ⟨60121453509820475564665517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40080969006546983709777011 60121453509820475564665517)
      ·
        refine ⟨22545545066182678336749569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60121453509820475564665517 22545545066182678336749569)
        ·
          refine ⟨16909158799637008752562177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22545545066182678336749569 16909158799637008752562177)
          ·
            refine ⟨12681869099727756564421633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16909158799637008752562177 12681869099727756564421633)
            ·
              refine ⟨9511401824795817423316225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12681869099727756564421633 9511401824795817423316225)
              ·
                refine ⟨7133551368596863067487169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9511401824795817423316225 7133551368596863067487169)
                ·
                  refine ⟨5350163526447647300615377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7133551368596863067487169 5350163526447647300615377)
                  ·
                    refine ⟨4012622644835735475461533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5350163526447647300615377 4012622644835735475461533)
                    ·
                      refine ⟨1504733491813400803298075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012622644835735475461533 1504733491813400803298075)
                      ·
                        rfl

theorem cell23_2930458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_2930458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930458 prefixEnd_2930458 := by exact prefixLift 2930458
  have htrace : WordTrace (prefixWord ++ tailWord_2930458) baseStart_2930458 baseEnd_2930458 := by
    simpa [prefixWord, tailWord_2930458, baseEnd_2930458] using wordTrace_append hprefix tailTrace_2930458
  have hstable : (prefixWord ++ tailWord_2930458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930458).length < 2 ^ (prefixWord ++ tailWord_2930458).sum := by decide
  have hdescent : baseEnd_2930458 < baseStart_2930458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930465 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2930465 : Nat := 118140960795 + 2930465 * 2 ^ 59
def prefixEnd_2930465 : Nat := 4983230072969 + 3 ^ 40 * 2930465 * 2
def baseEnd_2930465 : Nat := 501579028725994091970181

theorem tailTrace_2930465 : CollatzResearch.WordTrace tailWord_2930465 prefixEnd_2930465 501579028725994091970181 := by
  unfold tailWord_2930465
  simp only [CollatzResearch.WordTrace]
  refine ⟨106882839328433263421576849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71255226218955508947717899 106882839328433263421576849)
  ·
    refine ⟨80162129496324947566182637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106882839328433263421576849 80162129496324947566182637)
    ·
      refine ⟨30060798561121855337318489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80162129496324947566182637 30060798561121855337318489)
      ·
        refine ⟨22545598920841391502988867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30060798561121855337318489 22545598920841391502988867)
        ·
          refine ⟨33818398381262087254483301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22545598920841391502988867 33818398381262087254483301)
          ·
            refine ⟨6340949696486641360215619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33818398381262087254483301 6340949696486641360215619)
            ·
              refine ⟨9511424544729962040323429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340949696486641360215619 9511424544729962040323429)
              ·
                refine ⟨1783392102136867882560643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9511424544729962040323429 1783392102136867882560643)
                ·
                  refine ⟨2675088153205301823840965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783392102136867882560643 2675088153205301823840965)
                  ·
                    refine ⟨501579028725994091970181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675088153205301823840965 501579028725994091970181)
                    ·
                      rfl

theorem cell23_2930465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2930465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930465 prefixEnd_2930465 := by exact prefixLift 2930465
  have htrace : WordTrace (prefixWord ++ tailWord_2930465) baseStart_2930465 baseEnd_2930465 := by
    simpa [prefixWord, tailWord_2930465, baseEnd_2930465] using wordTrace_append hprefix tailTrace_2930465
  have hstable : (prefixWord ++ tailWord_2930465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930465).length < 2 ^ (prefixWord ++ tailWord_2930465).sum := by decide
  have hdescent : baseEnd_2930465 < baseStart_2930465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930488 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_2930488 : Nat := 118140960795 + 2930488 * 2 ^ 59
def prefixEnd_2930488 : Nat := 4983230072969 + 3 ^ 40 * 2930488 * 2
def baseEnd_2930488 : Nat := 1504748896233035685922937

theorem tailTrace_2930488 : CollatzResearch.WordTrace tailWord_2930488 prefixEnd_2930488 1504748896233035685922937 := by
  unfold tailWord_2930488
  simp only [CollatzResearch.WordTrace]
  refine ⟨53441839103674969174832059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71255785471566625566442745 53441839103674969174832059)
  ·
    refine ⟨80162758655512453762248089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53441839103674969174832059 80162758655512453762248089)
    ·
      refine ⟨60122068991634340321686067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80162758655512453762248089 60122068991634340321686067)
      ·
        refine ⟨90183103487451510482529101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60122068991634340321686067 90183103487451510482529101)
        ·
          refine ⟨33818663807794316430948413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90183103487451510482529101 33818663807794316430948413)
          ·
            refine ⟨12681998927922868661605655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33818663807794316430948413 12681998927922868661605655)
            ·
              refine ⟨19022998391884302992408483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12681998927922868661605655 19022998391884302992408483)
              ·
                refine ⟨28534497587826454488612725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19022998391884302992408483 28534497587826454488612725)
                ·
                  refine ⟨2675109148858730108307443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28534497587826454488612725 2675109148858730108307443)
                  ·
                    refine ⟨4012663723288095162461165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675109148858730108307443 4012663723288095162461165)
                    ·
                      refine ⟨1504748896233035685922937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012663723288095162461165 1504748896233035685922937)
                      ·
                        rfl

theorem cell23_2930488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_2930488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930488 prefixEnd_2930488 := by exact prefixLift 2930488
  have htrace : WordTrace (prefixWord ++ tailWord_2930488) baseStart_2930488 baseEnd_2930488 := by
    simpa [prefixWord, tailWord_2930488, baseEnd_2930488] using wordTrace_append hprefix tailTrace_2930488
  have hstable : (prefixWord ++ tailWord_2930488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930488).length < 2 ^ (prefixWord ++ tailWord_2930488).sum := by decide
  have hdescent : baseEnd_2930488 < baseStart_2930488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930545 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_2930545 : Nat := 118140960795 + 2930545 * 2 ^ 59
def prefixEnd_2930545 : Nat := 4983230072969 + 3 ^ 40 * 2930545 * 2
def baseEnd_2930545 : Nat := 1504778164630341962910175

theorem tailTrace_2930545 : CollatzResearch.WordTrace tailWord_2930545 prefixEnd_2930545 1504778164630341962910175 := by
  unfold tailWord_2930545
  simp only [CollatzResearch.WordTrace]
  refine ⟨106885757168143437084489089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71257171445428958056326059 106885757168143437084489089)
  ·
    refine ⟨80164317876107577813366817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106885757168143437084489089 80164317876107577813366817)
    ·
      refine ⟨60123238407080683360025113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80164317876107577813366817 60123238407080683360025113)
      ·
        refine ⟨45092428805310512520018835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60123238407080683360025113 45092428805310512520018835)
        ·
          refine ⟨67638643207965768780028253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45092428805310512520018835 67638643207965768780028253)
          ·
            refine ⟨25364491202987163292510595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67638643207965768780028253 25364491202987163292510595)
            ·
              refine ⟨38046736804480744938765893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25364491202987163292510595 38046736804480744938765893)
              ·
                refine ⟨7133763150840139676018605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38046736804480744938765893 7133763150840139676018605)
                ·
                  refine ⟨2675161181565052378506977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7133763150840139676018605 2675161181565052378506977)
                  ·
                    refine ⟨2006370886173789283880233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675161181565052378506977 2006370886173789283880233)
                    ·
                      refine ⟨1504778164630341962910175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006370886173789283880233 1504778164630341962910175)
                      ·
                        rfl

theorem cell23_2930545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_2930545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930545 prefixEnd_2930545 := by exact prefixLift 2930545
  have htrace : WordTrace (prefixWord ++ tailWord_2930545) baseStart_2930545 baseEnd_2930545 := by
    simpa [prefixWord, tailWord_2930545, baseEnd_2930545] using wordTrace_append hprefix tailTrace_2930545
  have hstable : (prefixWord ++ tailWord_2930545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930545).length < 2 ^ (prefixWord ++ tailWord_2930545).sum := by decide
  have hdescent : baseEnd_2930545 < baseStart_2930545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930568 : List Nat := [2, 1, 3, 3, 3, 2, 9]
def baseStart_2930568 : Nat := 118140960795 + 2930568 * 2 ^ 59
def prefixEnd_2930568 : Nat := 4983230072969 + 3 ^ 40 * 2930568 * 2
def baseEnd_2930568 : Nat := 18577654008461671270649

theorem tailTrace_2930568 : CollatzResearch.WordTrace tailWord_2930568 prefixEnd_2930568 18577654008461671270649 := by
  unfold tailWord_2930568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53443298023530056006288179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71257730698040074675050905 53443298023530056006288179)
  ·
    refine ⟨80164947035295084009432269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53443298023530056006288179 80164947035295084009432269)
    ·
      refine ⟨30061855138235656503537101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80164947035295084009432269 30061855138235656503537101)
      ·
        refine ⟨11273195676838371188826413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30061855138235656503537101 11273195676838371188826413)
        ·
          refine ⟨4227448378814389195809905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11273195676838371188826413 4227448378814389195809905)
          ·
            refine ⟨3170586284110791896857429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227448378814389195809905 3170586284110791896857429)
            ·
              refine ⟨18577654008461671270649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3170586284110791896857429 18577654008461671270649)
              ·
                rfl

theorem cell23_2930568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 9].length) (baseStart_2930568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930568 prefixEnd_2930568 := by exact prefixLift 2930568
  have htrace : WordTrace (prefixWord ++ tailWord_2930568) baseStart_2930568 baseEnd_2930568 := by
    simpa [prefixWord, tailWord_2930568, baseEnd_2930568] using wordTrace_append hprefix tailTrace_2930568
  have hstable : (prefixWord ++ tailWord_2930568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930568).length < 2 ^ (prefixWord ++ tailWord_2930568).sum := by decide
  have hdescent : baseEnd_2930568 < baseStart_2930568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930581 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2930581 : Nat := 118140960795 + 2930581 * 2 ^ 59
def prefixEnd_2930581 : Nat := 4983230072969 + 3 ^ 40 * 2930581 * 2
def baseEnd_2930581 : Nat := 501598883311301274020003

theorem tailTrace_2930581 : CollatzResearch.WordTrace tailWord_2930581 prefixEnd_2930581 501598883311301274020003 := by
  unfold tailWord_2930581
  simp only [CollatzResearch.WordTrace]
  refine ⟨106887070196013015232799597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71258046797342010155199731 106887070196013015232799597)
  ·
    refine ⟨40082651323504880712299849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106887070196013015232799597 40082651323504880712299849)
    ·
      refine ⟨30061988492628660534224887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40082651323504880712299849 30061988492628660534224887)
      ·
        refine ⟨45092982738942990801337331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30061988492628660534224887 45092982738942990801337331)
        ·
          refine ⟨67639474108414486202005997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45092982738942990801337331 67639474108414486202005997)
          ·
            refine ⟨25364802790655432325752249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67639474108414486202005997 25364802790655432325752249)
            ·
              refine ⟨19023602092991574244314187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25364802790655432325752249 19023602092991574244314187)
              ·
                refine ⟨28535403139487361366471281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19023602092991574244314187 28535403139487361366471281)
                ·
                  refine ⟨21401552354615521024853461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28535403139487361366471281 21401552354615521024853461)
                  ·
                    refine ⟨501598883311301274020003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21401552354615521024853461 501598883311301274020003)
                    ·
                      rfl

theorem cell23_2930581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2930581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930581 prefixEnd_2930581 := by exact prefixLift 2930581
  have htrace : WordTrace (prefixWord ++ tailWord_2930581) baseStart_2930581 baseEnd_2930581 := by
    simpa [prefixWord, tailWord_2930581, baseEnd_2930581] using wordTrace_append hprefix tailTrace_2930581
  have hstable : (prefixWord ++ tailWord_2930581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930581).length < 2 ^ (prefixWord ++ tailWord_2930581).sum := by decide
  have hdescent : baseEnd_2930581 < baseStart_2930581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930601 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2930601 : Nat := 118140960795 + 2930601 * 2 ^ 59
def prefixEnd_2930601 : Nat := 4983230072969 + 3 ^ 40 * 2930601 * 2
def baseEnd_2930601 : Nat := 1504806919546993743809917

theorem tailTrace_2930601 : CollatzResearch.WordTrace tailWord_2930601 prefixEnd_2930601 1504806919546993743809917 := by
  unfold tailWord_2930601
  simp only [CollatzResearch.WordTrace]
  refine ⟨106887799655940558648527657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71258533103960372432351771 106887799655940558648527657)
  ·
    refine ⟨80165849741955418986395743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106887799655940558648527657 80165849741955418986395743)
    ·
      refine ⟨120248774612933128479593615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80165849741955418986395743 120248774612933128479593615)
      ·
        refine ⟨180373161919399692719390423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120248774612933128479593615 180373161919399692719390423)
        ·
          refine ⟨270559742879099539079085635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180373161919399692719390423 270559742879099539079085635)
          ·
            refine ⟨405839614318649308618628453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270559742879099539079085635 405839614318649308618628453)
            ·
              refine ⟨76094927684746745365992835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405839614318649308618628453 76094927684746745365992835)
              ·
                refine ⟨114142391527120118048989253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76094927684746745365992835 114142391527120118048989253)
                ·
                  refine ⟨21401698411335022134185485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114142391527120118048989253 21401698411335022134185485)
                  ·
                    refine ⟨8025636904250633300319557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21401698411335022134185485 8025636904250633300319557)
                    ·
                      refine ⟨1504806919546993743809917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8025636904250633300319557 1504806919546993743809917)
                      ·
                        rfl

theorem cell23_2930601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2930601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930601 prefixEnd_2930601 := by exact prefixLift 2930601
  have htrace : WordTrace (prefixWord ++ tailWord_2930601) baseStart_2930601 baseEnd_2930601 := by
    simpa [prefixWord, tailWord_2930601, baseEnd_2930601] using wordTrace_append hprefix tailTrace_2930601
  have hstable : (prefixWord ++ tailWord_2930601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930601).length < 2 ^ (prefixWord ++ tailWord_2930601).sum := by decide
  have hdescent : baseEnd_2930601 < baseStart_2930601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930631 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2930631 : Nat := 118140960795 + 2930631 * 2 ^ 59
def prefixEnd_2930631 : Nat := 4983230072969 + 3 ^ 40 * 2930631 * 2
def baseEnd_2930631 : Nat := 1504822323966628626434779

theorem tailTrace_2930631 : CollatzResearch.WordTrace tailWord_2930631 prefixEnd_2930631 1504822323966628626434779 := by
  unfold tailWord_2930631
  simp only [CollatzResearch.WordTrace]
  refine ⟨106888893845831873772119747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71259262563887915848079831 106888893845831873772119747)
  ·
    refine ⟨160333340768747810658179621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106888893845831873772119747 160333340768747810658179621)
    ·
      refine ⟨30062501394140214498408679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160333340768747810658179621 30062501394140214498408679)
      ·
        refine ⟨45093752091210321747613019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30062501394140214498408679 45093752091210321747613019)
        ·
          refine ⟨67640628136815482621419529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45093752091210321747613019 67640628136815482621419529)
          ·
            refine ⟨50730471102611611966064647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67640628136815482621419529 50730471102611611966064647)
            ·
              refine ⟨76095706653917417949096971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50730471102611611966064647 76095706653917417949096971)
              ·
                refine ⟨114143559980876126923645457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76095706653917417949096971 114143559980876126923645457)
                ·
                  refine ⟨85607669985657095192734093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114143559980876126923645457 85607669985657095192734093)
                  ·
                    refine ⟨32102876244621410697275285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85607669985657095192734093 32102876244621410697275285)
                    ·
                      refine ⟨1504822323966628626434779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32102876244621410697275285 1504822323966628626434779)
                      ·
                        rfl

theorem cell23_2930631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2930631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930631 prefixEnd_2930631 := by exact prefixLift 2930631
  have htrace : WordTrace (prefixWord ++ tailWord_2930631) baseStart_2930631 baseEnd_2930631 := by
    simpa [prefixWord, tailWord_2930631, baseEnd_2930631] using wordTrace_append hprefix tailTrace_2930631
  have hstable : (prefixWord ++ tailWord_2930631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930631).length < 2 ^ (prefixWord ++ tailWord_2930631).sum := by decide
  have hdescent : baseEnd_2930631 < baseStart_2930631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930638 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2930638 : Nat := 118140960795 + 2930638 * 2 ^ 59
def prefixEnd_2930638 : Nat := 4983230072969 + 3 ^ 40 * 2930638 * 2
def baseEnd_2930638 : Nat := 1504825918331210099047247

theorem tailTrace_2930638 : CollatzResearch.WordTrace tailWord_2930638 prefixEnd_2930638 1504825918331210099047247 := by
  unfold tailWord_2930638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361143644600814245953071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71259432771204342645083045 13361143644600814245953071)
  ·
    refine ⟨20041715466901221368929607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13361143644600814245953071 20041715466901221368929607)
    ·
      refine ⟨30062573200351832053394411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20041715466901221368929607 30062573200351832053394411)
      ·
        refine ⟨45093859800527748080091617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30062573200351832053394411 45093859800527748080091617)
        ·
          refine ⟨33820394850395811060068713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45093859800527748080091617 33820394850395811060068713)
          ·
            refine ⟨25365296137796858295051535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33820394850395811060068713 25365296137796858295051535)
            ·
              refine ⟨38047944206695287442577303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25365296137796858295051535 38047944206695287442577303)
              ·
                refine ⟨57071916310042931163865955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38047944206695287442577303 57071916310042931163865955)
                ·
                  refine ⟨85607874465064396745798933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57071916310042931163865955 85607874465064396745798933)
                  ·
                    refine ⟨4012869115549893597459325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85607874465064396745798933 4012869115549893597459325)
                    ·
                      refine ⟨1504825918331210099047247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4012869115549893597459325 1504825918331210099047247)
                      ·
                        rfl

theorem cell23_2930638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2930638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930638 prefixEnd_2930638 := by exact prefixLift 2930638
  have htrace : WordTrace (prefixWord ++ tailWord_2930638) baseStart_2930638 baseEnd_2930638 := by
    simpa [prefixWord, tailWord_2930638, baseEnd_2930638] using wordTrace_append hprefix tailTrace_2930638
  have hstable : (prefixWord ++ tailWord_2930638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930638).length < 2 ^ (prefixWord ++ tailWord_2930638).sum := by decide
  have hdescent : baseEnd_2930638 < baseStart_2930638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930648 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2930648 : Nat := 118140960795 + 2930648 * 2 ^ 59
def prefixEnd_2930648 : Nat := 4983230072969 + 3 ^ 40 * 2930648 * 2
def baseEnd_2930648 : Nat := 1504831053137755059922201

theorem tailTrace_2930648 : CollatzResearch.WordTrace tailWord_2930648 prefixEnd_2930648 1504831053137755059922201 := by
  unfold tailWord_2930648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53444756943385142837744299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71259675924513523783659065 53444756943385142837744299)
  ·
    refine ⟨80167135415077714256616449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53444756943385142837744299 80167135415077714256616449)
    ·
      refine ⟨60125351561308285692462337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80167135415077714256616449 60125351561308285692462337)
      ·
        refine ⟨45094013670981214269346753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60125351561308285692462337 45094013670981214269346753)
        ·
          refine ⟨33820510253235910702010065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45094013670981214269346753 33820510253235910702010065)
          ·
            refine ⟨25365382689926933026507549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33820510253235910702010065 25365382689926933026507549)
            ·
              refine ⟨9512018508722599884940331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25365382689926933026507549 9512018508722599884940331)
              ·
                refine ⟨14268027763083899827410497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512018508722599884940331 14268027763083899827410497)
                ·
                  refine ⟨10701020822312924870557873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14268027763083899827410497 10701020822312924870557873)
                  ·
                    refine ⟨8025765616734693652918405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10701020822312924870557873 8025765616734693652918405)
                    ·
                      refine ⟨1504831053137755059922201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8025765616734693652918405 1504831053137755059922201)
                      ·
                        rfl

theorem cell23_2930648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2930648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930648 prefixEnd_2930648 := by exact prefixLift 2930648
  have htrace : WordTrace (prefixWord ++ tailWord_2930648) baseStart_2930648 baseEnd_2930648 := by
    simpa [prefixWord, tailWord_2930648, baseEnd_2930648] using wordTrace_append hprefix tailTrace_2930648
  have hstable : (prefixWord ++ tailWord_2930648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930648).length < 2 ^ (prefixWord ++ tailWord_2930648).sum := by decide
  have hdescent : baseEnd_2930648 < baseStart_2930648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930686 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2930686 : Nat := 118140960795 + 2930686 * 2 ^ 59
def prefixEnd_2930686 : Nat := 4983230072969 + 3 ^ 40 * 2930686 * 2
def baseEnd_2930686 : Nat := 1504850565402625911247027

theorem tailTrace_2930686 : CollatzResearch.WordTrace tailWord_2930686 prefixEnd_2930686 1504850565402625911247027 := by
  unfold tailWord_2930686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361362482579077270671489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71260599907088412110247941 13361362482579077270671489)
  ·
    refine ⟨10021021861934307953003617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13361362482579077270671489 10021021861934307953003617)
    ·
      refine ⟨7515766396450730964752713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021021861934307953003617 7515766396450730964752713)
      ·
        refine ⟨5636824797338048223564535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7515766396450730964752713 5636824797338048223564535)
        ·
          refine ⟨8455237196007072335346803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636824797338048223564535 8455237196007072335346803)
          ·
            refine ⟨12682855794010608503020205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455237196007072335346803 12682855794010608503020205)
            ·
              refine ⟨4756070922753978188632577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12682855794010608503020205 4756070922753978188632577)
              ·
                refine ⟨3567053192065483641474433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756070922753978188632577 3567053192065483641474433)
                ·
                  refine ⟨2675289894049112731105825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567053192065483641474433 2675289894049112731105825)
                  ·
                    refine ⟨2006467420536834548329369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675289894049112731105825 2006467420536834548329369)
                    ·
                      refine ⟨1504850565402625911247027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006467420536834548329369 1504850565402625911247027)
                      ·
                        rfl

theorem cell23_2930686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2930686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930686 prefixEnd_2930686 := by exact prefixLift 2930686
  have htrace : WordTrace (prefixWord ++ tailWord_2930686) baseStart_2930686 baseEnd_2930686 := by
    simpa [prefixWord, tailWord_2930686, baseEnd_2930686] using wordTrace_append hprefix tailTrace_2930686
  have hstable : (prefixWord ++ tailWord_2930686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930686).length < 2 ^ (prefixWord ++ tailWord_2930686).sum := by decide
  have hdescent : baseEnd_2930686 < baseStart_2930686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930692 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 7]
def baseStart_2930692 : Nat := 118140960795 + 2930692 * 2 ^ 59
def prefixEnd_2930692 : Nat := 4983230072969 + 3 ^ 40 * 2930692 * 2
def baseEnd_2930692 : Nat := 167205960698505876419111

theorem tailTrace_2930692 : CollatzResearch.WordTrace tailWord_2930692 prefixEnd_2930692 167205960698505876419111 := by
  unfold tailWord_2930692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53445559349305440595045165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71260745799073920793393553 53445559349305440595045165)
  ·
    refine ⟨20042084755989540223141937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53445559349305440595045165 20042084755989540223141937)
    ·
      refine ⟨15031563566992155167356453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20042084755989540223141937 15031563566992155167356453)
      ·
        refine ⟨2818418168811029093879335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15031563566992155167356453 2818418168811029093879335)
        ·
          refine ⟨4227627253216543640819003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818418168811029093879335 4227627253216543640819003)
          ·
            refine ⟨6341440879824815461228505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227627253216543640819003 6341440879824815461228505)
            ·
              refine ⟨4756080659868611595921379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6341440879824815461228505 4756080659868611595921379)
              ·
                refine ⟨7134120989802917393882069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756080659868611595921379 7134120989802917393882069)
                ·
                  refine ⟨167205960698505876419111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7134120989802917393882069 167205960698505876419111)
                  ·
                    rfl

theorem cell23_2930692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_2930692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930692 prefixEnd_2930692 := by exact prefixLift 2930692
  have htrace : WordTrace (prefixWord ++ tailWord_2930692) baseStart_2930692 baseEnd_2930692 := by
    simpa [prefixWord, tailWord_2930692, baseEnd_2930692] using wordTrace_append hprefix tailTrace_2930692
  have hstable : (prefixWord ++ tailWord_2930692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930692).length < 2 ^ (prefixWord ++ tailWord_2930692).sum := by decide
  have hdescent : baseEnd_2930692 < baseStart_2930692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930742 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2930742 : Nat := 118140960795 + 2930742 * 2 ^ 59
def prefixEnd_2930742 : Nat := 4983230072969 + 3 ^ 40 * 2930742 * 2
def baseEnd_2930742 : Nat := 1504879320319277692146769

theorem tailTrace_2930742 : CollatzResearch.WordTrace tailWord_2930742 prefixEnd_2930742 1504879320319277692146769 := by
  unfold tailWord_2930742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680808896776858733088155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71261961565619826486273653 6680808896776858733088155)
  ·
    refine ⟨10021213345165288099632233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680808896776858733088155 10021213345165288099632233)
    ·
      refine ⟨7515910008873966074724175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021213345165288099632233 7515910008873966074724175)
      ·
        refine ⟨11273865013310949112086263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7515910008873966074724175 11273865013310949112086263)
        ·
          refine ⟨16910797519966423668129395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11273865013310949112086263 16910797519966423668129395)
          ·
            refine ⟨25366196279949635502194093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16910797519966423668129395 25366196279949635502194093)
            ·
              refine ⟨9512323604981113313322785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25366196279949635502194093 9512323604981113313322785)
              ·
                refine ⟨7134242703735834984992089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512323604981113313322785 7134242703735834984992089)
                ·
                  refine ⟨5350682027801876238744067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7134242703735834984992089 5350682027801876238744067)
                  ·
                    refine ⟨8026023041702814358116101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350682027801876238744067 8026023041702814358116101)
                    ·
                      refine ⟨1504879320319277692146769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8026023041702814358116101 1504879320319277692146769)
                      ·
                        rfl

theorem cell23_2930742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2930742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930742 prefixEnd_2930742 := by exact prefixLift 2930742
  have htrace : WordTrace (prefixWord ++ tailWord_2930742) baseStart_2930742 baseEnd_2930742 := by
    simpa [prefixWord, tailWord_2930742, baseEnd_2930742] using wordTrace_append hprefix tailTrace_2930742
  have hstable : (prefixWord ++ tailWord_2930742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930742).length < 2 ^ (prefixWord ++ tailWord_2930742).sum := by decide
  have hdescent : baseEnd_2930742 < baseStart_2930742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930748 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 8]
def baseStart_2930748 : Nat := 118140960795 + 2930748 * 2 ^ 59
def prefixEnd_2930748 : Nat := 4983230072969 + 3 ^ 40 * 2930748 * 2
def baseEnd_2930748 : Nat := 167209155689244963185749

theorem tailTrace_2930748 : CollatzResearch.WordTrace tailWord_2930748 prefixEnd_2930748 167209155689244963185749 := by
  unfold tailWord_2930748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53446580593204001377064449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71262107457605335169419265 53446580593204001377064449)
  ·
    refine ⟨40084935444903001032798337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53446580593204001377064449 40084935444903001032798337)
    ·
      refine ⟨30063701583677250774598753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40084935444903001032798337 30063701583677250774598753)
      ·
        refine ⟨22547776187757938080949065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30063701583677250774598753 22547776187757938080949065)
        ·
          refine ⟨16910832140818453560711799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22547776187757938080949065 16910832140818453560711799)
          ·
            refine ⟨25366248211227680341067699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16910832140818453560711799 25366248211227680341067699)
            ·
              refine ⟨38049372316841520511601549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25366248211227680341067699 38049372316841520511601549)
              ·
                refine ⟨14268514618815570191850581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38049372316841520511601549 14268514618815570191850581)
                ·
                  refine ⟨167209155689244963185749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14268514618815570191850581 167209155689244963185749)
                  ·
                    rfl

theorem cell23_2930748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_2930748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930748 prefixEnd_2930748 := by exact prefixLift 2930748
  have htrace : WordTrace (prefixWord ++ tailWord_2930748) baseStart_2930748 baseEnd_2930748 := by
    simpa [prefixWord, tailWord_2930748, baseEnd_2930748] using wordTrace_append hprefix tailTrace_2930748
  have hstable : (prefixWord ++ tailWord_2930748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930748).length < 2 ^ (prefixWord ++ tailWord_2930748).sum := by decide
  have hdescent : baseEnd_2930748 < baseStart_2930748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930752 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_2930752 : Nat := 118140960795 + 2930752 * 2 ^ 59
def prefixEnd_2930752 : Nat := 4983230072969 + 3 ^ 40 * 2930752 * 2
def baseEnd_2930752 : Nat := 501628151708607551007241

theorem tailTrace_2930752 : CollatzResearch.WordTrace tailWord_2930752 prefixEnd_2930752 501628151708607551007241 := by
  unfold tailWord_2930752
  simp only [CollatzResearch.WordTrace]
  refine ⟨53446653539196755718637255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71262204718929007624849673 53446653539196755718637255)
  ·
    refine ⟨80169980308795133577955883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53446653539196755718637255 80169980308795133577955883)
    ·
      refine ⟨120254970463192700366933825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80169980308795133577955883 120254970463192700366933825)
      ·
        refine ⟨90191227847394525275200369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120254970463192700366933825 90191227847394525275200369)
        ·
          refine ⟨67643420885545893956400277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90191227847394525275200369 67643420885545893956400277)
          ·
            refine ⟨3170785354009963779206263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67643420885545893956400277 3170785354009963779206263)
            ·
              refine ⟨4756178031014945668809395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170785354009963779206263 4756178031014945668809395)
              ·
                refine ⟨7134267046522418503214093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756178031014945668809395 7134267046522418503214093)
                ·
                  refine ⟨2675350142445906938705285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7134267046522418503214093 2675350142445906938705285)
                  ·
                    refine ⟨501628151708607551007241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675350142445906938705285 501628151708607551007241)
                    ·
                      rfl

theorem cell23_2930752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_2930752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930752 prefixEnd_2930752 := by exact prefixLift 2930752
  have htrace : WordTrace (prefixWord ++ tailWord_2930752) baseStart_2930752 baseEnd_2930752 := by
    simpa [prefixWord, tailWord_2930752, baseEnd_2930752] using wordTrace_append hprefix tailTrace_2930752
  have hstable : (prefixWord ++ tailWord_2930752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930752).length < 2 ^ (prefixWord ++ tailWord_2930752).sum := by decide
  have hdescent : baseEnd_2930752 < baseStart_2930752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930808 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_2930808 : Nat := 118140960795 + 2930808 * 2 ^ 59
def prefixEnd_2930808 : Nat := 4983230072969 + 3 ^ 40 * 2930808 * 2
def baseEnd_2930808 : Nat := 501637736680824811307155

theorem tailTrace_2930808 : CollatzResearch.WordTrace tailWord_2930808 prefixEnd_2930808 501637736680824811307155 := by
  unfold tailWord_2930808
  simp only [CollatzResearch.WordTrace]
  refine ⟨53447674783095316500656539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71263566377460422000875385 53447674783095316500656539)
  ·
    refine ⟨80171512174642974750984809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53447674783095316500656539 80171512174642974750984809)
    ·
      refine ⟨60128634130982231063238607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80171512174642974750984809 60128634130982231063238607)
      ·
        refine ⟨90192951196473346594857911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60128634130982231063238607 90192951196473346594857911)
        ·
          refine ⟨135289426794710019892286867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90192951196473346594857911 135289426794710019892286867)
          ·
            refine ⟨202934140192065029838430301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135289426794710019892286867 202934140192065029838430301)
            ·
              refine ⟨76100302572024386189411363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202934140192065029838430301 76100302572024386189411363)
              ·
                refine ⟨114150453858036579284117045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76100302572024386189411363 114150453858036579284117045)
                ·
                  refine ⟨10701605049190929307885973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114150453858036579284117045 10701605049190929307885973)
                  ·
                    refine ⟨501637736680824811307155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10701605049190929307885973 501637736680824811307155)
                    ·
                      rfl

theorem cell23_2930808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_2930808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930808 prefixEnd_2930808 := by exact prefixLift 2930808
  have htrace : WordTrace (prefixWord ++ tailWord_2930808) baseStart_2930808 baseEnd_2930808 := by
    simpa [prefixWord, tailWord_2930808, baseEnd_2930808] using wordTrace_append hprefix tailTrace_2930808
  have hstable : (prefixWord ++ tailWord_2930808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930808).length < 2 ^ (prefixWord ++ tailWord_2930808).sum := by decide
  have hdescent : baseEnd_2930808 < baseStart_2930808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930825 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_2930825 : Nat := 118140960795 + 2930825 * 2 ^ 59
def prefixEnd_2930825 : Nat := 4983230072969 + 3 ^ 40 * 2930825 * 2
def baseEnd_2930825 : Nat := 501640646404533622469629

theorem tailTrace_2930825 : CollatzResearch.WordTrace tailWord_2930825 prefixEnd_2930825 501640646404533622469629 := by
  unfold tailWord_2930825
  simp only [CollatzResearch.WordTrace]
  refine ⟨106895969607129044904681929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71263979738086029936454619 106895969607129044904681929)
  ·
    refine ⟨80171977205346783678511447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106895969607129044904681929 80171977205346783678511447)
    ·
      refine ⟨120257965808020175517767171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80171977205346783678511447 120257965808020175517767171)
      ·
        refine ⟨180386948712030263276650757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120257965808020175517767171 180386948712030263276650757)
        ·
          refine ⟨33822552883505674364372017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180386948712030263276650757 33822552883505674364372017)
          ·
            refine ⟨25366914662629255773279013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33822552883505674364372017 25366914662629255773279013)
            ·
              refine ⟨4756296499242985457489815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25366914662629255773279013 4756296499242985457489815)
              ·
                refine ⟨7134444748864478186234723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756296499242985457489815 7134444748864478186234723)
                ·
                  refine ⟨10701667123296717279352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134444748864478186234723 10701667123296717279352085)
                  ·
                    refine ⟨501640646404533622469629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10701667123296717279352085 501640646404533622469629)
                    ·
                      rfl

theorem cell23_2930825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_2930825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930825 prefixEnd_2930825 := by exact prefixLift 2930825
  have htrace : WordTrace (prefixWord ++ tailWord_2930825) baseStart_2930825 baseEnd_2930825 := by
    simpa [prefixWord, tailWord_2930825, baseEnd_2930825] using wordTrace_append hprefix tailTrace_2930825
  have hstable : (prefixWord ++ tailWord_2930825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930825).length < 2 ^ (prefixWord ++ tailWord_2930825).sum := by decide
  have hdescent : baseEnd_2930825 < baseStart_2930825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930836 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2930836 : Nat := 118140960795 + 2930836 * 2 ^ 59
def prefixEnd_2930836 : Nat := 4983230072969 + 3 ^ 40 * 2930836 * 2
def baseEnd_2930836 : Nat := 1504927587500800324371337

theorem tailTrace_2930836 : CollatzResearch.WordTrace tailWord_2930836 prefixEnd_2930836 1504927587500800324371337 := by
  unfold tailWord_2930836
  simp only [CollatzResearch.WordTrace]
  refine ⟨53448185405044596891666181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71264247206726129188888241 53448185405044596891666181)
  ·
    refine ⟨10021534763445861917187409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53448185405044596891666181 10021534763445861917187409)
    ·
      refine ⟨7516151072584396437890557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021534763445861917187409 7516151072584396437890557)
      ·
        refine ⟨2818556652219148664208959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7516151072584396437890557 2818556652219148664208959)
        ·
          refine ⟨4227834978328722996313439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818556652219148664208959 4227834978328722996313439)
          ·
            refine ⟨6341752467493084494470159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227834978328722996313439 6341752467493084494470159)
            ·
              refine ⟨9512628701239626741705239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341752467493084494470159 9512628701239626741705239)
              ·
                refine ⟨14268943051859440112557859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512628701239626741705239 14268943051859440112557859)
                ·
                  refine ⟨21403414577789160168836789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14268943051859440112557859 21403414577789160168836789)
                  ·
                    refine ⟨2006570116667733765828449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21403414577789160168836789 2006570116667733765828449)
                    ·
                      refine ⟨1504927587500800324371337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006570116667733765828449 1504927587500800324371337)
                      ·
                        rfl

theorem cell23_2930836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2930836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930836 prefixEnd_2930836 := by exact prefixLift 2930836
  have htrace : WordTrace (prefixWord ++ tailWord_2930836) baseStart_2930836 baseEnd_2930836 := by
    simpa [prefixWord, tailWord_2930836, baseEnd_2930836] using wordTrace_append hprefix tailTrace_2930836
  have hstable : (prefixWord ++ tailWord_2930836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930836).length < 2 ^ (prefixWord ++ tailWord_2930836).sum := by decide
  have hdescent : baseEnd_2930836 < baseStart_2930836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930849 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2930849 : Nat := 118140960795 + 2930849 * 2 ^ 59
def prefixEnd_2930849 : Nat := 4983230072969 + 3 ^ 40 * 2930849 * 2
def baseEnd_2930849 : Nat := 1504934262749308773508777

theorem tailTrace_2930849 : CollatzResearch.WordTrace tailWord_2930849 prefixEnd_2930849 1504934262749308773508777 := by
  unfold tailWord_2930849
  simp only [CollatzResearch.WordTrace]
  refine ⟨106896844959042097003555601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71264563306028064669037067 106896844959042097003555601)
  ·
    refine ⟨80172633719281572752666701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106896844959042097003555601 80172633719281572752666701)
    ·
      refine ⟨30064737644730589782250013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80172633719281572752666701 30064737644730589782250013)
      ·
        refine ⟨11274276616773971168343755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30064737644730589782250013 11274276616773971168343755)
        ·
          refine ⟨16911414925160956752515633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11274276616773971168343755 16911414925160956752515633)
          ·
            refine ⟨12683561193870717564386725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16911414925160956752515633 12683561193870717564386725)
            ·
              refine ⟨2378167723850759543322511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12683561193870717564386725 2378167723850759543322511)
              ·
                refine ⟨3567251585776139314983767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378167723850759543322511 3567251585776139314983767)
                ·
                  refine ⟨5350877378664208972475651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567251585776139314983767 5350877378664208972475651)
                  ·
                    refine ⟨8026316067996313458713477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350877378664208972475651 8026316067996313458713477)
                    ·
                      refine ⟨1504934262749308773508777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8026316067996313458713477 1504934262749308773508777)
                      ·
                        rfl

theorem cell23_2930849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2930849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930849 prefixEnd_2930849 := by exact prefixLift 2930849
  have htrace : WordTrace (prefixWord ++ tailWord_2930849) baseStart_2930849 baseEnd_2930849 := by
    simpa [prefixWord, tailWord_2930849, baseEnd_2930849] using wordTrace_append hprefix tailTrace_2930849
  have hstable : (prefixWord ++ tailWord_2930849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930849).length < 2 ^ (prefixWord ++ tailWord_2930849).sum := by decide
  have hdescent : baseEnd_2930849 < baseStart_2930849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930866 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_2930866 : Nat := 118140960795 + 2930866 * 2 ^ 59
def prefixEnd_2930866 : Nat := 4983230072969 + 3 ^ 40 * 2930866 * 2
def baseEnd_2930866 : Nat := 1504942991920435206996199

theorem tailTrace_2930866 : CollatzResearch.WordTrace tailWord_2930866 prefixEnd_2930866 1504942991920435206996199 := by
  unfold tailWord_2930866
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724366249995127226731113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71264976666653672604616301 26724366249995127226731113)
  ·
    refine ⟨20043274687496345420048335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26724366249995127226731113 20043274687496345420048335)
    ·
      refine ⟨30064912031244518130072503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20043274687496345420048335 30064912031244518130072503)
      ·
        refine ⟨45097368046866777195108755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30064912031244518130072503 45097368046866777195108755)
        ·
          refine ⟨67646052070300165792663133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45097368046866777195108755 67646052070300165792663133)
          ·
            refine ⟨25367269526362562172248675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67646052070300165792663133 25367269526362562172248675)
            ·
              refine ⟨38050904289543843258373013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25367269526362562172248675 38050904289543843258373013)
              ·
                refine ⟨1783636138572367652736235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38050904289543843258373013 1783636138572367652736235)
                ·
                  refine ⟨2675454207858551479104353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783636138572367652736235 2675454207858551479104353)
                  ·
                    refine ⟨2006590655893913609328265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675454207858551479104353 2006590655893913609328265)
                    ·
                      refine ⟨1504942991920435206996199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006590655893913609328265 1504942991920435206996199)
                      ·
                        rfl

theorem cell23_2930866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_2930866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930866 prefixEnd_2930866 := by exact prefixLift 2930866
  have htrace : WordTrace (prefixWord ++ tailWord_2930866) baseStart_2930866 baseEnd_2930866 := by
    simpa [prefixWord, tailWord_2930866, baseEnd_2930866] using wordTrace_append hprefix tailTrace_2930866
  have hstable : (prefixWord ++ tailWord_2930866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930866).length < 2 ^ (prefixWord ++ tailWord_2930866).sum := by decide
  have hdescent : baseEnd_2930866 < baseStart_2930866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930869 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2930869 : Nat := 118140960795 + 2930869 * 2 ^ 59
def prefixEnd_2930869 : Nat := 4983230072969 + 3 ^ 40 * 2930869 * 2
def baseEnd_2930869 : Nat := 1504944532362398695258685

theorem tailTrace_2930869 : CollatzResearch.WordTrace tailWord_2930869 prefixEnd_2930869 1504944532362398695258685 := by
  unfold tailWord_2930869
  simp only [CollatzResearch.WordTrace]
  refine ⟨106897574418969640419283661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71265049612646426946189107 106897574418969640419283661)
  ·
    refine ⟨40086590407113615157231373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106897574418969640419283661 40086590407113615157231373)
    ·
      refine ⟨15032471402667605683961765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40086590407113615157231373 15032471402667605683961765)
      ·
        refine ⟨2818588388000176065742831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15032471402667605683961765 2818588388000176065742831)
        ·
          refine ⟨4227882582000264098614247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818588388000176065742831 4227882582000264098614247)
          ·
            refine ⟨6341823873000396147921371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227882582000264098614247 6341823873000396147921371)
            ·
              refine ⟨9512735809500594221882057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341823873000396147921371 9512735809500594221882057)
              ·
                refine ⟨7134551857125445666411543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512735809500594221882057 7134551857125445666411543)
                ·
                  refine ⟨10701827785688168499617315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134551857125445666411543 10701827785688168499617315)
                  ·
                    refine ⟨16052741678532252749425973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10701827785688168499617315 16052741678532252749425973)
                    ·
                      refine ⟨1504944532362398695258685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16052741678532252749425973 1504944532362398695258685)
                      ·
                        rfl

theorem cell23_2930869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2930869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930869 prefixEnd_2930869 := by exact prefixLift 2930869
  have htrace : WordTrace (prefixWord ++ tailWord_2930869) baseStart_2930869 baseEnd_2930869 := by
    simpa [prefixWord, tailWord_2930869, baseEnd_2930869] using wordTrace_append hprefix tailTrace_2930869
  have hstable : (prefixWord ++ tailWord_2930869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930869).length < 2 ^ (prefixWord ++ tailWord_2930869).sum := by decide
  have hdescent : baseEnd_2930869 < baseStart_2930869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930876 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_2930876 : Nat := 118140960795 + 2930876 * 2 ^ 59
def prefixEnd_2930876 : Nat := 4983230072969 + 3 ^ 40 * 2930876 * 2
def baseEnd_2930876 : Nat := 501649375575660055957051

theorem tailTrace_2930876 : CollatzResearch.WordTrace tailWord_2930876 prefixEnd_2930876 501649375575660055957051 := by
  unfold tailWord_2930876
  simp only [CollatzResearch.WordTrace]
  refine ⟨53448914864972140307394241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71265219819962853743192321 53448914864972140307394241)
  ·
    refine ⟨40086686148729105230545681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53448914864972140307394241 40086686148729105230545681)
    ·
      refine ⟨30065014611546828922909261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40086686148729105230545681 30065014611546828922909261)
      ·
        refine ⟨11274380479330060846090973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30065014611546828922909261 11274380479330060846090973)
        ·
          refine ⟨4227892679748772817284115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11274380479330060846090973 4227892679748772817284115)
          ·
            refine ⟨6341839019623159225926173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227892679748772817284115 6341839019623159225926173)
            ·
              refine ⟨2378189632358684709722315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6341839019623159225926173 2378189632358684709722315)
              ·
                refine ⟨3567284448538027064583473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378189632358684709722315 3567284448538027064583473)
                ·
                  refine ⟨2675463336403520298437605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567284448538027064583473 2675463336403520298437605)
                  ·
                    refine ⟨501649375575660055957051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675463336403520298437605 501649375575660055957051)
                    ·
                      rfl

theorem cell23_2930876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_2930876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930876 prefixEnd_2930876 := by exact prefixLift 2930876
  have htrace : WordTrace (prefixWord ++ tailWord_2930876) baseStart_2930876 baseEnd_2930876 := by
    simpa [prefixWord, tailWord_2930876, baseEnd_2930876] using wordTrace_append hprefix tailTrace_2930876
  have hstable : (prefixWord ++ tailWord_2930876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930876).length < 2 ^ (prefixWord ++ tailWord_2930876).sum := by decide
  have hdescent : baseEnd_2930876 < baseStart_2930876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930942 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2930942 : Nat := 118140960795 + 2930942 * 2 ^ 59
def prefixEnd_2930942 : Nat := 4983230072969 + 3 ^ 40 * 2930942 * 2
def baseEnd_2930942 : Nat := 1504982016450176909645849

theorem tailTrace_2930942 : CollatzResearch.WordTrace tailWord_2930942 prefixEnd_2930942 1504982016450176909645849 := by
  unfold tailWord_2930942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362529618463146735836385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71266824631803449257794053 13362529618463146735836385)
  ·
    refine ⟨10021897213847360051877289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13362529618463146735836385 10021897213847360051877289)
    ·
      refine ⟨7516422910385520038907967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021897213847360051877289 7516422910385520038907967)
      ·
        refine ⟨11274634365578280058361951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516422910385520038907967 11274634365578280058361951)
        ·
          refine ⟨16911951548367420087542927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11274634365578280058361951 16911951548367420087542927)
          ·
            refine ⟨25367927322551130131314391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16911951548367420087542927 25367927322551130131314391)
            ·
              refine ⟨38051890983826695196971587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25367927322551130131314391 38051890983826695196971587)
              ·
                refine ⟨57077836475740042795457381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38051890983826695196971587 57077836475740042795457381)
                ·
                  refine ⟨10702094339201258024148259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57077836475740042795457381 10702094339201258024148259)
                  ·
                    refine ⟨16053141508801887036222389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10702094339201258024148259 16053141508801887036222389)
                    ·
                      refine ⟨1504982016450176909645849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16053141508801887036222389 1504982016450176909645849)
                      ·
                        rfl

theorem cell23_2930942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2930942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930942 prefixEnd_2930942 := by exact prefixLift 2930942
  have htrace : WordTrace (prefixWord ++ tailWord_2930942) baseStart_2930942 baseEnd_2930942 := by
    simpa [prefixWord, tailWord_2930942, baseEnd_2930942] using wordTrace_append hprefix tailTrace_2930942
  have hstable : (prefixWord ++ tailWord_2930942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930942).length < 2 ^ (prefixWord ++ tailWord_2930942).sum := by decide
  have hdescent : baseEnd_2930942 < baseStart_2930942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930945 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 9]
def baseStart_2930945 : Nat := 118140960795 + 2930945 * 2 ^ 59
def prefixEnd_2930945 : Nat := 4983230072969 + 3 ^ 40 * 2930945 * 2
def baseEnd_2930945 : Nat := 167220395210237821989815

theorem tailTrace_2930945 : CollatzResearch.WordTrace tailWord_2930945 prefixEnd_2930945 167220395210237821989815 := by
  unfold tailWord_2930945
  simp only [CollatzResearch.WordTrace]
  refine ⟨106900346366694305399050289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71266897577796203599366859 106900346366694305399050289)
  ·
    refine ⟨80175259775020729049287717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106900346366694305399050289 80175259775020729049287717)
    ·
      refine ⟨15032861207816386696741447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80175259775020729049287717 15032861207816386696741447)
      ·
        refine ⟨22549291811724580045112171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032861207816386696741447 22549291811724580045112171)
        ·
          refine ⟨33823937717586870067668257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22549291811724580045112171 33823937717586870067668257)
          ·
            refine ⟨25367953288190152550751193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33823937717586870067668257 25367953288190152550751193)
            ·
              refine ⟨19025964966142614413063395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25367953288190152550751193 19025964966142614413063395)
              ·
                refine ⟨28538947449213921619595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19025964966142614413063395 28538947449213921619595093)
                ·
                  refine ⟨167220395210237821989815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28538947449213921619595093 167220395210237821989815)
                  ·
                    rfl

theorem cell23_2930945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_2930945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930945 prefixEnd_2930945 := by exact prefixLift 2930945
  have htrace : WordTrace (prefixWord ++ tailWord_2930945) baseStart_2930945 baseEnd_2930945 := by
    simpa [prefixWord, tailWord_2930945, baseEnd_2930945] using wordTrace_append hprefix tailTrace_2930945
  have hstable : (prefixWord ++ tailWord_2930945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930945).length < 2 ^ (prefixWord ++ tailWord_2930945).sum := by decide
  have hdescent : baseEnd_2930945 < baseStart_2930945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2930972 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2930972 : Nat := 118140960795 + 2930972 * 2 ^ 59
def prefixEnd_2930972 : Nat := 4983230072969 + 3 ^ 40 * 2930972 * 2
def baseEnd_2930972 : Nat := 1504997420869811792270711

theorem tailTrace_2930972 : CollatzResearch.WordTrace tailWord_2930972 prefixEnd_2930972 1504997420869811792270711 := by
  unfold tailWord_2930972
  simp only [CollatzResearch.WordTrace]
  refine ⟨53450665568798244505141585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71267554091730992673522113 53450665568798244505141585)
  ·
    refine ⟨40087999176598683378856189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53450665568798244505141585 40087999176598683378856189)
    ·
      refine ⟨15032999691224506267071071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40087999176598683378856189 15032999691224506267071071)
      ·
        refine ⟨22549499536836759400606607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15032999691224506267071071 22549499536836759400606607)
        ·
          refine ⟨33824249305255139100909911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22549499536836759400606607 33824249305255139100909911)
          ·
            refine ⟨50736373957882708651364867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33824249305255139100909911 50736373957882708651364867)
            ·
              refine ⟨76104560936824062977047301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50736373957882708651364867 76104560936824062977047301)
              ·
                refine ⟨14269605175654511808196369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76104560936824062977047301 14269605175654511808196369)
                ·
                  refine ⟨10702203881740883856147277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14269605175654511808196369 10702203881740883856147277)
                  ·
                    refine ⟨4013326455652831446055229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10702203881740883856147277 4013326455652831446055229)
                    ·
                      refine ⟨1504997420869811792270711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4013326455652831446055229 1504997420869811792270711)
                      ·
                        rfl

theorem cell23_2930972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2930972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2930972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2930972 prefixEnd_2930972 := by exact prefixLift 2930972
  have htrace : WordTrace (prefixWord ++ tailWord_2930972) baseStart_2930972 baseEnd_2930972 := by
    simpa [prefixWord, tailWord_2930972, baseEnd_2930972] using wordTrace_append hprefix tailTrace_2930972
  have hstable : (prefixWord ++ tailWord_2930972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2930972).length < 2 ^ (prefixWord ++ tailWord_2930972).sum := by decide
  have hdescent : baseEnd_2930972 < baseStart_2930972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2930972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931009 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2931009 : Nat := 118140960795 + 2931009 * 2 ^ 59
def prefixEnd_2931009 : Nat := 4983230072969 + 3 ^ 40 * 2931009 * 2
def baseEnd_2931009 : Nat := 501672139884676049169347

theorem tailTrace_2931009 : CollatzResearch.WordTrace tailWord_2931009 prefixEnd_2931009 501672139884676049169347 := by
  unfold tailWord_2931009
  simp only [CollatzResearch.WordTrace]
  refine ⟨106902680638462444329380081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71268453758974962886253387 106902680638462444329380081)
  ·
    refine ⟨80177010478846833247035061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106902680638462444329380081 80177010478846833247035061)
    ·
      refine ⟨7516594732391890616909537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80177010478846833247035061 7516594732391890616909537)
      ·
        refine ⟨5637446049293917962682153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7516594732391890616909537 5637446049293917962682153)
        ·
          refine ⟨4228084536970438472011615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5637446049293917962682153 4228084536970438472011615)
          ·
            refine ⟨6342126805455657708017423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228084536970438472011615 6342126805455657708017423)
            ·
              refine ⟨9513190208183486562026135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342126805455657708017423 9513190208183486562026135)
              ·
                refine ⟨14269785312275229843039203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9513190208183486562026135 14269785312275229843039203)
                ·
                  refine ⟨21404677968412844764558805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14269785312275229843039203 21404677968412844764558805)
                  ·
                    refine ⟨501672139884676049169347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21404677968412844764558805 501672139884676049169347)
                    ·
                      rfl

theorem cell23_2931009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2931009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931009 prefixEnd_2931009 := by exact prefixLift 2931009
  have htrace : WordTrace (prefixWord ++ tailWord_2931009) baseStart_2931009 baseEnd_2931009 := by
    simpa [prefixWord, tailWord_2931009, baseEnd_2931009] using wordTrace_append hprefix tailTrace_2931009
  have hstable : (prefixWord ++ tailWord_2931009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931009).length < 2 ^ (prefixWord ++ tailWord_2931009).sum := by decide
  have hdescent : baseEnd_2931009 < baseStart_2931009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931073 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2931073 : Nat := 118140960795 + 2931073 * 2 ^ 59
def prefixEnd_2931073 : Nat := 4983230072969 + 3 ^ 40 * 2931073 * 2
def baseEnd_2931073 : Nat := 501683094138638632369249

theorem tailTrace_2931073 : CollatzResearch.WordTrace tailWord_2931073 prefixEnd_2931073 501683094138638632369249 := by
  unfold tailWord_2931073
  simp only [CollatzResearch.WordTrace]
  refine ⟨106905014910230583259709873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71270009940153722173139915 106905014910230583259709873)
  ·
    refine ⟨80178761182672937444782405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106905014910230583259709873 80178761182672937444782405)
    ·
      refine ⟨15033517721751175770896701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80178761182672937444782405 15033517721751175770896701)
      ·
        refine ⟨5637569145656690914086263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15033517721751175770896701 5637569145656690914086263)
        ·
          refine ⟨8456353718485036371129395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637569145656690914086263 8456353718485036371129395)
          ·
            refine ⟨12684530577727554556694093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8456353718485036371129395 12684530577727554556694093)
            ·
              refine ⟨4756698966647832958760285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12684530577727554556694093 4756698966647832958760285)
              ·
                refine ⟨1783762112492937359535107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4756698966647832958760285 1783762112492937359535107)
                ·
                  refine ⟨2675643168739406039302661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783762112492937359535107 2675643168739406039302661)
                  ·
                    refine ⟨501683094138638632369249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675643168739406039302661 501683094138638632369249)
                    ·
                      rfl

theorem cell23_2931073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2931073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931073 prefixEnd_2931073 := by exact prefixLift 2931073
  have htrace : WordTrace (prefixWord ++ tailWord_2931073) baseStart_2931073 baseEnd_2931073 := by
    simpa [prefixWord, tailWord_2931073, baseEnd_2931073] using wordTrace_append hprefix tailTrace_2931073
  have hstable : (prefixWord ++ tailWord_2931073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931073).length < 2 ^ (prefixWord ++ tailWord_2931073).sum := by decide
  have hdescent : baseEnd_2931073 < baseStart_2931073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931106 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2931106 : Nat := 118140960795 + 2931106 * 2 ^ 59
def prefixEnd_2931106 : Nat := 4983230072969 + 3 ^ 40 * 2931106 * 2
def baseEnd_2931106 : Nat := 1505066227277514267995095

theorem tailTrace_2931106 : CollatzResearch.WordTrace tailWord_2931106 prefixEnd_2931106 1505066227277514267995095 := by
  unfold tailWord_2931106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26726554629777757473915293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71270812346074019930440781 26726554629777757473915293)
  ·
    refine ⟨10022457986166659052718235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26726554629777757473915293 10022457986166659052718235)
    ·
      refine ⟨15033686979249988579077353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10022457986166659052718235 15033686979249988579077353)
      ·
        refine ⟨11275265234437491434308015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15033686979249988579077353 11275265234437491434308015)
        ·
          refine ⟨16912897851656237151462023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11275265234437491434308015 16912897851656237151462023)
          ·
            refine ⟨25369346777484355727193035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16912897851656237151462023 25369346777484355727193035)
            ·
              refine ⟨38054020166226533590789553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25369346777484355727193035 38054020166226533590789553)
              ·
                refine ⟨28540515124669900193092165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38054020166226533590789553 28540515124669900193092165)
                ·
                  refine ⟨5351346585875606286204781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28540515124669900193092165 5351346585875606286204781)
                  ·
                    refine ⟨2006754969703352357326793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5351346585875606286204781 2006754969703352357326793)
                    ·
                      refine ⟨1505066227277514267995095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006754969703352357326793 1505066227277514267995095)
                      ·
                        rfl

theorem cell23_2931106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2931106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931106 prefixEnd_2931106 := by exact prefixLift 2931106
  have htrace : WordTrace (prefixWord ++ tailWord_2931106) baseStart_2931106 baseEnd_2931106 := by
    simpa [prefixWord, tailWord_2931106, baseEnd_2931106] using wordTrace_append hprefix tailTrace_2931106
  have hstable : (prefixWord ++ tailWord_2931106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931106).length < 2 ^ (prefixWord ++ tailWord_2931106).sum := by decide
  have hdescent : baseEnd_2931106 < baseStart_2931106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931129 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_2931129 : Nat := 118140960795 + 2931129 * 2 ^ 59
def prefixEnd_2931129 : Nat := 4983230072969 + 3 ^ 40 * 2931129 * 2
def baseEnd_2931129 : Nat := 501692679110855892669163

theorem tailTrace_2931129 : CollatzResearch.WordTrace tailWord_2931129 prefixEnd_2931129 501692679110855892669163 := by
  unfold tailWord_2931129
  simp only [CollatzResearch.WordTrace]
  refine ⟨106907057398027704823748441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71271371598685136549165627 106907057398027704823748441)
  ·
    refine ⟨80180293048520778617811331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106907057398027704823748441 80180293048520778617811331)
    ·
      refine ⟨120270439572781167926716997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80180293048520778617811331 120270439572781167926716997)
      ·
        refine ⟨22550707419896468986259437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120270439572781167926716997 22550707419896468986259437)
        ·
          refine ⟨8456515282461175869847289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22550707419896468986259437 8456515282461175869847289)
          ·
            refine ⟨6342386461845881902385467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8456515282461175869847289 6342386461845881902385467)
            ·
              refine ⟨9513579692768822853578201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342386461845881902385467 9513579692768822853578201)
              ·
                refine ⟨7135184769576617140183651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9513579692768822853578201 7135184769576617140183651)
                ·
                  refine ⟨10702777154364925710275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7135184769576617140183651 10702777154364925710275477)
                  ·
                    refine ⟨501692679110855892669163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10702777154364925710275477 501692679110855892669163)
                    ·
                      rfl

theorem cell23_2931129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_2931129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931129 prefixEnd_2931129 := by exact prefixLift 2931129
  have htrace : WordTrace (prefixWord ++ tailWord_2931129) baseStart_2931129 baseEnd_2931129 := by
    simpa [prefixWord, tailWord_2931129, baseEnd_2931129] using wordTrace_append hprefix tailTrace_2931129
  have hstable : (prefixWord ++ tailWord_2931129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931129).length < 2 ^ (prefixWord ++ tailWord_2931129).sum := by decide
  have hdescent : baseEnd_2931129 < baseStart_2931129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931146 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_2931146 : Nat := 118140960795 + 2931146 * 2 ^ 59
def prefixEnd_2931146 : Nat := 4983230072969 + 3 ^ 40 * 2931146 * 2
def baseEnd_2931146 : Nat := 501695588834564703831637

theorem tailTrace_2931146 : CollatzResearch.WordTrace tailWord_2931146 prefixEnd_2931146 501695588834564703831637 := by
  unfold tailWord_2931146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26726919359741529181779323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71271784959310744484744861 26726919359741529181779323)
  ·
    refine ⟨40090379039612293772668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26726919359741529181779323 40090379039612293772668985)
    ·
      refine ⟨30067784279709220329501739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40090379039612293772668985 30067784279709220329501739)
      ·
        refine ⟨45101676419563830494252609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30067784279709220329501739 45101676419563830494252609)
        ·
          refine ⟨33826257314672872870689457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45101676419563830494252609 33826257314672872870689457)
          ·
            refine ⟨25369692986004654653017093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33826257314672872870689457 25369692986004654653017093)
            ·
              refine ⟨4756817434875872747440705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25369692986004654653017093 4756817434875872747440705)
              ·
                refine ⟨3567613076156904560580529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756817434875872747440705 3567613076156904560580529)
                ·
                  refine ⟨2675709807117678420435397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567613076156904560580529 2675709807117678420435397)
                  ·
                    refine ⟨501695588834564703831637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675709807117678420435397 501695588834564703831637)
                    ·
                      rfl

theorem cell23_2931146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_2931146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931146 prefixEnd_2931146 := by exact prefixLift 2931146
  have htrace : WordTrace (prefixWord ++ tailWord_2931146) baseStart_2931146 baseEnd_2931146 := by
    simpa [prefixWord, tailWord_2931146, baseEnd_2931146] using wordTrace_append hprefix tailTrace_2931146
  have hstable : (prefixWord ++ tailWord_2931146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931146).length < 2 ^ (prefixWord ++ tailWord_2931146).sum := by decide
  have hdescent : baseEnd_2931146 < baseStart_2931146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931156 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2931156 : Nat := 118140960795 + 2931156 * 2 ^ 59
def prefixEnd_2931156 : Nat := 4983230072969 + 3 ^ 40 * 2931156 * 2
def baseEnd_2931156 : Nat := 1505091901310239072369865

theorem tailTrace_2931156 : CollatzResearch.WordTrace tailWord_2931156 prefixEnd_2931156 1505091901310239072369865 := by
  unfold tailWord_2931156
  simp only [CollatzResearch.WordTrace]
  refine ⟨53454021084464944217490661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71272028112619925623320881 53454021084464944217490661)
  ·
    refine ⟨10022628953337177040779499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53454021084464944217490661 10022628953337177040779499)
    ·
      refine ⟨15033943430005765561169249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10022628953337177040779499 15033943430005765561169249)
      ·
        refine ⟨11275457572504324170876937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15033943430005765561169249 11275457572504324170876937)
        ·
          refine ⟨8456593179378243128157703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11275457572504324170876937 8456593179378243128157703)
          ·
            refine ⟨12684889769067364692236555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8456593179378243128157703 12684889769067364692236555)
            ·
              refine ⟨19027334653601047038354833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12684889769067364692236555 19027334653601047038354833)
              ·
                refine ⟨14270500990200785278766125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19027334653601047038354833 14270500990200785278766125)
                ·
                  refine ⟨5351437871325294479537297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14270500990200785278766125 5351437871325294479537297)
                  ·
                    refine ⟨4013578403493970859652973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5351437871325294479537297 4013578403493970859652973)
                    ·
                      refine ⟨1505091901310239072369865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4013578403493970859652973 1505091901310239072369865)
                      ·
                        rfl

theorem cell23_2931156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2931156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931156 prefixEnd_2931156 := by exact prefixLift 2931156
  have htrace : WordTrace (prefixWord ++ tailWord_2931156) baseStart_2931156 baseEnd_2931156 := by
    simpa [prefixWord, tailWord_2931156, baseEnd_2931156] using wordTrace_append hprefix tailTrace_2931156
  have hstable : (prefixWord ++ tailWord_2931156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931156).length < 2 ^ (prefixWord ++ tailWord_2931156).sum := by decide
  have hdescent : baseEnd_2931156 < baseStart_2931156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931220 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2931220 : Nat := 118140960795 + 2931220 * 2 ^ 59
def prefixEnd_2931220 : Nat := 4983230072969 + 3 ^ 40 * 2931220 * 2
def baseEnd_2931220 : Nat := 1505124764072126821969571

theorem tailTrace_2931220 : CollatzResearch.WordTrace tailWord_2931220 prefixEnd_2931220 1505124764072126821969571 := by
  unfold tailWord_2931220
  simp only [CollatzResearch.WordTrace]
  refine ⟨53455188220349013682655557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71273584293798684910207409 53455188220349013682655557)
  ·
    refine ⟨10022847791315440065497917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53455188220349013682655557 10022847791315440065497917)
    ·
      refine ⟨3758567921743290024561719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10022847791315440065497917 3758567921743290024561719)
      ·
        refine ⟨5637851882614935036842579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758567921743290024561719 5637851882614935036842579)
        ·
          refine ⟨8456777823922402555263869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637851882614935036842579 8456777823922402555263869)
          ·
            refine ⟨3171291683970900958223951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8456777823922402555263869 3171291683970900958223951)
            ·
              refine ⟨4756937525956351437335927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171291683970900958223951 4756937525956351437335927)
              ·
                refine ⟨7135406288934527156003891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4756937525956351437335927 7135406288934527156003891)
                ·
                  refine ⟨10703109433401790734005837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7135406288934527156003891 10703109433401790734005837)
                  ·
                    refine ⟨4013666037525671525252189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10703109433401790734005837 4013666037525671525252189)
                    ·
                      refine ⟨1505124764072126821969571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4013666037525671525252189 1505124764072126821969571)
                      ·
                        rfl

theorem cell23_2931220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2931220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931220 prefixEnd_2931220 := by exact prefixLift 2931220
  have htrace : WordTrace (prefixWord ++ tailWord_2931220) baseStart_2931220 baseEnd_2931220 := by
    simpa [prefixWord, tailWord_2931220, baseEnd_2931220] using wordTrace_append hprefix tailTrace_2931220
  have hstable : (prefixWord ++ tailWord_2931220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931220).length < 2 ^ (prefixWord ++ tailWord_2931220).sum := by decide
  have hdescent : baseEnd_2931220 < baseStart_2931220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931277 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_2931277 : Nat := 118140960795 + 2931277 * 2 ^ 59
def prefixEnd_2931277 : Nat := 4983230072969 + 3 ^ 40 * 2931277 * 2
def baseEnd_2931277 : Nat := 1505154032469433098956809

theorem tailTrace_2931277 : CollatzResearch.WordTrace tailWord_2931277 prefixEnd_2931277 1505154032469433098956809 := by
  unfold tailWord_2931277
  simp only [CollatzResearch.WordTrace]
  refine ⟨106912455401491526100136085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71274970267661017400090723 106912455401491526100136085)
  ·
    refine ⟨5011521346944915285943879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106912455401491526100136085 5011521346944915285943879)
    ·
      refine ⟨7517282020417372928915819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011521346944915285943879 7517282020417372928915819)
      ·
        refine ⟨11275923030626059393373729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517282020417372928915819 11275923030626059393373729)
        ·
          refine ⟨8456942272969544545030297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11275923030626059393373729 8456942272969544545030297)
          ·
            refine ⟨6342706704727158408772723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8456942272969544545030297 6342706704727158408772723)
            ·
              refine ⟨9514060057090737613159085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342706704727158408772723 9514060057090737613159085)
              ·
                refine ⟨3567772521409026604934657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9514060057090737613159085 3567772521409026604934657)
                ·
                  refine ⟨2675829391056769953700993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567772521409026604934657 2675829391056769953700993)
                  ·
                    refine ⟨2006872043292577465275745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2675829391056769953700993 2006872043292577465275745)
                    ·
                      refine ⟨1505154032469433098956809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006872043292577465275745 1505154032469433098956809)
                      ·
                        rfl

theorem cell23_2931277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_2931277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931277 prefixEnd_2931277 := by exact prefixLift 2931277
  have htrace : WordTrace (prefixWord ++ tailWord_2931277) baseStart_2931277 baseEnd_2931277 := by
    simpa [prefixWord, tailWord_2931277, baseEnd_2931277] using wordTrace_append hprefix tailTrace_2931277
  have hstable : (prefixWord ++ tailWord_2931277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931277).length < 2 ^ (prefixWord ++ tailWord_2931277).sum := by decide
  have hdescent : baseEnd_2931277 < baseStart_2931277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931294 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2931294 : Nat := 118140960795 + 2931294 * 2 ^ 59
def prefixEnd_2931294 : Nat := 4983230072969 + 3 ^ 40 * 2931294 * 2
def baseEnd_2931294 : Nat := 1505162761640559532444231

theorem tailTrace_2931294 : CollatzResearch.WordTrace tailWord_2931294 prefixEnd_2931294 1505162761640559532444231 := by
  unfold tailWord_2931294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364134430303742250438117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71275383628286625335669957 13364134430303742250438117)
  ·
    refine ⟨2505775205681951671957147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13364134430303742250438117 2505775205681951671957147)
    ·
      refine ⟨3758662808522927507935721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2505775205681951671957147 3758662808522927507935721)
      ·
        refine ⟨2818997106392195630951791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758662808522927507935721 2818997106392195630951791)
        ·
          refine ⟨4228495659588293446427687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818997106392195630951791 4228495659588293446427687)
          ·
            refine ⟨6342743489382440169641531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228495659588293446427687 6342743489382440169641531)
            ·
              refine ⟨9514115234073660254462297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342743489382440169641531 9514115234073660254462297)
              ·
                refine ⟨7135586425555245190846723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9514115234073660254462297 7135586425555245190846723)
                ·
                  refine ⟨10703379638332867786270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7135586425555245190846723 10703379638332867786270085)
                  ·
                    refine ⟨2006883682187412709925641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10703379638332867786270085 2006883682187412709925641)
                    ·
                      refine ⟨1505162761640559532444231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006883682187412709925641 1505162761640559532444231)
                      ·
                        rfl

theorem cell23_2931294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2931294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931294 prefixEnd_2931294 := by exact prefixLift 2931294
  have htrace : WordTrace (prefixWord ++ tailWord_2931294) baseStart_2931294 baseEnd_2931294 := by
    simpa [prefixWord, tailWord_2931294, baseEnd_2931294] using wordTrace_append hprefix tailTrace_2931294
  have hstable : (prefixWord ++ tailWord_2931294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931294).length < 2 ^ (prefixWord ++ tailWord_2931294).sum := by decide
  have hdescent : baseEnd_2931294 < baseStart_2931294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931317 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 5]
def baseStart_2931317 : Nat := 118140960795 + 2931317 * 2 ^ 59
def prefixEnd_2931317 : Nat := 4983230072969 + 3 ^ 40 * 2931317 * 2
def baseEnd_2931317 : Nat := 167241619077290326939625

theorem tailTrace_2931317 : CollatzResearch.WordTrace tailWord_2931317 prefixEnd_2931317 167241619077290326939625 := by
  unfold tailWord_2931317
  simp only [CollatzResearch.WordTrace]
  refine ⟨106913914321346612931592205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71275942880897741954394803 106913914321346612931592205)
  ·
    refine ⟨40092717870504979849347077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106913914321346612931592205 40092717870504979849347077)
    ·
      refine ⟨7517384600719683721752577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40092717870504979849347077 7517384600719683721752577)
      ·
        refine ⟨5638038450539762791314433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7517384600719683721752577 5638038450539762791314433)
        ·
          refine ⟨4228528837904822093485825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5638038450539762791314433 4228528837904822093485825)
          ·
            refine ⟨3171396628428616570114369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4228528837904822093485825 3171396628428616570114369)
            ·
              refine ⟨2378547471321462427585777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171396628428616570114369 2378547471321462427585777)
              ·
                refine ⟨1783910603491096820689333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378547471321462427585777 1783910603491096820689333)
                ·
                  refine ⟨167241619077290326939625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1783910603491096820689333 167241619077290326939625)
                  ·
                    rfl

theorem cell23_2931317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_2931317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931317 prefixEnd_2931317 := by exact prefixLift 2931317
  have htrace : WordTrace (prefixWord ++ tailWord_2931317) baseStart_2931317 baseEnd_2931317 := by
    simpa [prefixWord, tailWord_2931317, baseEnd_2931317] using wordTrace_append hprefix tailTrace_2931317
  have hstable : (prefixWord ++ tailWord_2931317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931317).length < 2 ^ (prefixWord ++ tailWord_2931317).sum := by decide
  have hdescent : baseEnd_2931317 < baseStart_2931317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931333 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_2931333 : Nat := 118140960795 + 2931333 * 2 ^ 59
def prefixEnd_2931333 : Nat := 4983230072969 + 3 ^ 40 * 2931333 * 2
def baseEnd_2931333 : Nat := 1505182787386084879856551

theorem tailTrace_2931333 : CollatzResearch.WordTrace tailWord_2931333 prefixEnd_2931333 1505182787386084879856551 := by
  unfold tailWord_2931333
  simp only [CollatzResearch.WordTrace]
  refine ⟨106914497889288647664174653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71276331926192431776116435 106914497889288647664174653)
  ·
    refine ⟨40092936708483242874065495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106914497889288647664174653 40092936708483242874065495)
    ·
      refine ⟨60139405062724864311098243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40092936708483242874065495 60139405062724864311098243)
      ·
        refine ⟨90209107594087296466647365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60139405062724864311098243 90209107594087296466647365)
        ·
          refine ⟨16914207673891368087496381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90209107594087296466647365 16914207673891368087496381)
          ·
            refine ⟨6342827877709263032811143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16914207673891368087496381 6342827877709263032811143)
            ·
              refine ⟨9514241816563894549216715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342827877709263032811143 9514241816563894549216715)
              ·
                refine ⟨14271362724845841823825073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514241816563894549216715 14271362724845841823825073)
                ·
                  refine ⟨10703522043634381367868805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14271362724845841823825073 10703522043634381367868805)
                  ·
                    refine ⟨2006910383181446506475401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10703522043634381367868805 2006910383181446506475401)
                    ·
                      refine ⟨1505182787386084879856551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2006910383181446506475401 1505182787386084879856551)
                      ·
                        rfl

theorem cell23_2931333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_2931333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931333 prefixEnd_2931333 := by exact prefixLift 2931333
  have htrace : WordTrace (prefixWord ++ tailWord_2931333) baseStart_2931333 baseEnd_2931333 := by
    simpa [prefixWord, tailWord_2931333, baseEnd_2931333] using wordTrace_append hprefix tailTrace_2931333
  have hstable : (prefixWord ++ tailWord_2931333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931333).length < 2 ^ (prefixWord ++ tailWord_2931333).sum := by decide
  have hdescent : baseEnd_2931333 < baseStart_2931333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931373 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 6]
def baseStart_2931373 : Nat := 118140960795 + 2931373 * 2 ^ 59
def prefixEnd_2931373 : Nat := 4983230072969 + 3 ^ 40 * 2931373 * 2
def baseEnd_2931373 : Nat := 167244814068029413706263

theorem tailTrace_2931373 : CollatzResearch.WordTrace tailWord_2931373 prefixEnd_2931373 167244814068029413706263 := by
  unfold tailWord_2931373
  simp only [CollatzResearch.WordTrace]
  refine ⟨106915956809143734495630773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71277304539429156330420515 106915956809143734495630773)
  ·
    refine ⟨10023370950857225108965385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106915956809143734495630773 10023370950857225108965385)
    ·
      refine ⟨7517528213142918831724039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10023370950857225108965385 7517528213142918831724039)
      ·
        refine ⟨11276292319714378247586059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517528213142918831724039 11276292319714378247586059)
        ·
          refine ⟨16914438479571567371379089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11276292319714378247586059 16914438479571567371379089)
          ·
            refine ⟨12685828859678675528534317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16914438479571567371379089 12685828859678675528534317)
            ·
              refine ⟨4757185822379503323200369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12685828859678675528534317 4757185822379503323200369)
              ·
                refine ⟨3567889366784627492400277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757185822379503323200369 3567889366784627492400277)
                ·
                  refine ⟨167244814068029413706263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3567889366784627492400277 167244814068029413706263)
                  ·
                    rfl

theorem cell23_2931373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_2931373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931373 prefixEnd_2931373 := by exact prefixLift 2931373
  have htrace : WordTrace (prefixWord ++ tailWord_2931373) baseStart_2931373 baseEnd_2931373 := by
    simpa [prefixWord, tailWord_2931373, baseEnd_2931373] using wordTrace_append hprefix tailTrace_2931373
  have hstable : (prefixWord ++ tailWord_2931373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931373).length < 2 ^ (prefixWord ++ tailWord_2931373).sum := by decide
  have hdescent : baseEnd_2931373 < baseStart_2931373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931419 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_2931419 : Nat := 118140960795 + 2931419 * 2 ^ 59
def prefixEnd_2931419 : Nat := 4983230072969 + 3 ^ 40 * 2931419 * 2
def baseEnd_2931419 : Nat := 1505226946722371543381155

theorem tailTrace_2931419 : CollatzResearch.WordTrace tailWord_2931419 prefixEnd_2931419 1505226946722371543381155 := by
  unfold tailWord_2931419
  simp only [CollatzResearch.WordTrace]
  refine ⟨106917634566977084351805311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71278423044651389567870207 106917634566977084351805311)
  ·
    refine ⟨160376451850465626527707967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106917634566977084351805311 160376451850465626527707967)
    ·
      refine ⟨240564677775698439791561951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160376451850465626527707967 240564677775698439791561951)
      ·
        refine ⟨360847016663547659687342927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240564677775698439791561951 360847016663547659687342927)
        ·
          refine ⟨541270524995321489531014391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360847016663547659687342927 541270524995321489531014391)
          ·
            refine ⟨811905787492982234296521587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541270524995321489531014391 811905787492982234296521587)
            ·
              refine ⟨1217858681239473351444782381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811905787492982234296521587 1217858681239473351444782381)
              ·
                refine ⟨456697005464802506791793393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1217858681239473351444782381 456697005464802506791793393)
                ·
                  refine ⟨342522754098601880093845045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456697005464802506791793393 342522754098601880093845045)
                  ·
                    refine ⟨32111508196743926258797973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342522754098601880093845045 32111508196743926258797973)
                    ·
                      refine ⟨1505226946722371543381155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32111508196743926258797973 1505226946722371543381155)
                      ·
                        rfl

theorem cell23_2931419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_2931419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931419 prefixEnd_2931419 := by exact prefixLift 2931419
  have htrace : WordTrace (prefixWord ++ tailWord_2931419) baseStart_2931419 baseEnd_2931419 := by
    simpa [prefixWord, tailWord_2931419, baseEnd_2931419] using wordTrace_append hprefix tailTrace_2931419
  have hstable : (prefixWord ++ tailWord_2931419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931419).length < 2 ^ (prefixWord ++ tailWord_2931419).sum := by decide
  have hdescent : baseEnd_2931419 < baseStart_2931419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931420 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2931420 : Nat := 118140960795 + 2931420 * 2 ^ 59
def prefixEnd_2931420 : Nat := 4983230072969 + 3 ^ 40 * 2931420 * 2
def baseEnd_2931420 : Nat := 501742486734342013156217

theorem tailTrace_2931420 : CollatzResearch.WordTrace tailWord_2931420 prefixEnd_2931420 501742486734342013156217 := by
  unfold tailWord_2931420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53458835519986730761295857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71278447359982307681727809 53458835519986730761295857)
  ·
    refine ⟨40094126639990048070971893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53458835519986730761295857 40094126639990048070971893)
    ·
      refine ⟨3758824372499067006653615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40094126639990048070971893 3758824372499067006653615)
      ·
        refine ⟨5638236558748600509980423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758824372499067006653615 5638236558748600509980423)
        ·
          refine ⟨8457354838122900764970635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638236558748600509980423 8457354838122900764970635)
          ·
            refine ⟨12686032257184351147455953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457354838122900764970635 12686032257184351147455953)
            ·
              refine ⟨9514524192888263360591965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12686032257184351147455953 9514524192888263360591965)
              ·
                refine ⟨3567946572333098760221987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9514524192888263360591965 3567946572333098760221987)
                ·
                  refine ⟨5351919858499648140332981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567946572333098760221987 5351919858499648140332981)
                  ·
                    refine ⟨501742486734342013156217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5351919858499648140332981 501742486734342013156217)
                    ·
                      rfl

theorem cell23_2931420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2931420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931420 prefixEnd_2931420 := by exact prefixLift 2931420
  have htrace : WordTrace (prefixWord ++ tailWord_2931420) baseStart_2931420 baseEnd_2931420 := by
    simpa [prefixWord, tailWord_2931420, baseEnd_2931420] using wordTrace_append hprefix tailTrace_2931420
  have hstable : (prefixWord ++ tailWord_2931420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931420).length < 2 ^ (prefixWord ++ tailWord_2931420).sum := by decide
  have hdescent : baseEnd_2931420 < baseStart_2931420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931423 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_2931423 : Nat := 118140960795 + 2931423 * 2 ^ 59
def prefixEnd_2931423 : Nat := 4983230072969 + 3 ^ 40 * 2931423 * 2
def baseEnd_2931423 : Nat := 1505229000644989527731137

theorem tailTrace_2931423 : CollatzResearch.WordTrace tailWord_2931423 prefixEnd_2931423 1505229000644989527731137 := by
  unfold tailWord_2931423
  simp only [CollatzResearch.WordTrace]
  refine ⟨106917780458962593034950923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71278520305975062023300615 106917780458962593034950923)
  ·
    refine ⟨160376670688443889552426385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106917780458962593034950923 160376670688443889552426385)
    ·
      refine ⟨120282503016332917164319789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160376670688443889552426385 120282503016332917164319789)
      ·
        refine ⟨45105938631124843936619921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120282503016332917164319789 45105938631124843936619921)
        ·
          refine ⟨33829453973343632952464941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45105938631124843936619921 33829453973343632952464941)
          ·
            refine ⟨12686045240003862357174353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33829453973343632952464941 12686045240003862357174353)
            ·
              refine ⟨9514533930002896767880765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12686045240003862357174353 9514533930002896767880765)
              ·
                refine ⟨3567950223751086287955287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9514533930002896767880765 3567950223751086287955287)
                ·
                  refine ⟨5351925335626629431932931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567950223751086287955287 5351925335626629431932931)
                  ·
                    refine ⟨8027888003439944147899397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5351925335626629431932931 8027888003439944147899397)
                    ·
                      refine ⟨1505229000644989527731137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8027888003439944147899397 1505229000644989527731137)
                      ·
                        rfl

theorem cell23_2931423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_2931423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931423 prefixEnd_2931423 := by exact prefixLift 2931423
  have htrace : WordTrace (prefixWord ++ tailWord_2931423) baseStart_2931423 baseEnd_2931423 := by
    simpa [prefixWord, tailWord_2931423, baseEnd_2931423] using wordTrace_append hprefix tailTrace_2931423
  have hstable : (prefixWord ++ tailWord_2931423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931423).length < 2 ^ (prefixWord ++ tailWord_2931423).sum := by decide
  have hdescent : baseEnd_2931423 < baseStart_2931423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931450 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_2931450 : Nat := 118140960795 + 2931450 * 2 ^ 59
def prefixEnd_2931450 : Nat := 4983230072969 + 3 ^ 40 * 2931450 * 2
def baseEnd_2931450 : Nat := 501747621540886974031171

theorem tailTrace_2931450 : CollatzResearch.WordTrace tailWord_2931450 prefixEnd_2931450 501747621540886974031171 := by
  unfold tailWord_2931450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729691307466194161545951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71279176819909851097455869 26729691307466194161545951)
  ·
    refine ⟨40094536961199291242318927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26729691307466194161545951 40094536961199291242318927)
    ·
      refine ⟨60141805441798936863478391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40094536961199291242318927 60141805441798936863478391)
      ·
        refine ⟨90212708162698405295217587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60141805441798936863478391 90212708162698405295217587)
        ·
          refine ⟨135319062244047607942826381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90212708162698405295217587 135319062244047607942826381)
          ·
            refine ⟨50744648341517852978559893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135319062244047607942826381 50744648341517852978559893)
            ·
              refine ⟨2378655391008649358369995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50744648341517852978559893 2378655391008649358369995)
              ·
                refine ⟨3567983086512974037554993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378655391008649358369995 3567983086512974037554993)
                ·
                  refine ⟨2675987314884730528166245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3567983086512974037554993 2675987314884730528166245)
                  ·
                    refine ⟨501747621540886974031171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675987314884730528166245 501747621540886974031171)
                    ·
                      rfl

theorem cell23_2931450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_2931450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931450 prefixEnd_2931450 := by exact prefixLift 2931450
  have htrace : WordTrace (prefixWord ++ tailWord_2931450) baseStart_2931450 baseEnd_2931450 := by
    simpa [prefixWord, tailWord_2931450, baseEnd_2931450] using wordTrace_append hprefix tailTrace_2931450
  have hstable : (prefixWord ++ tailWord_2931450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931450).length < 2 ^ (prefixWord ++ tailWord_2931450).sum := by decide
  have hdescent : baseEnd_2931450 < baseStart_2931450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931473 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_2931473 : Nat := 118140960795 + 2931473 * 2 ^ 59
def prefixEnd_2931473 : Nat := 4983230072969 + 3 ^ 40 * 2931473 * 2
def baseEnd_2931473 : Nat := 1505254674677714332105907

theorem tailTrace_2931473 : CollatzResearch.WordTrace tailWord_2931473 prefixEnd_2931473 1505254674677714332105907 := by
  unfold tailWord_2931473
  simp only [CollatzResearch.WordTrace]
  refine ⟨106919604108781451574271073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71279736072520967716180715 106919604108781451574271073)
  ·
    refine ⟨80189703081586088680703305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106919604108781451574271073 80189703081586088680703305)
    ·
      refine ⟨60142277311189566510527479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80189703081586088680703305 60142277311189566510527479)
      ·
        refine ⟨90213415966784349765791219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60142277311189566510527479 90213415966784349765791219)
        ·
          refine ⟨135320123950176524648686829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90213415966784349765791219 135320123950176524648686829)
          ·
            refine ⟨50745046481316196743257561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135320123950176524648686829 50745046481316196743257561)
            ·
              refine ⟨38058784860987147557443171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50745046481316196743257561 38058784860987147557443171)
              ·
                refine ⟨57088177291480721336164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38058784860987147557443171 57088177291480721336164757)
                ·
                  refine ⟨2676008310538158812632723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57088177291480721336164757 2676008310538158812632723)
                  ·
                    refine ⟨4014012465807238218949085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676008310538158812632723 4014012465807238218949085)
                    ·
                      refine ⟨1505254674677714332105907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014012465807238218949085 1505254674677714332105907)
                      ·
                        rfl

theorem cell23_2931473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_2931473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931473 prefixEnd_2931473 := by exact prefixLift 2931473
  have htrace : WordTrace (prefixWord ++ tailWord_2931473) baseStart_2931473 baseEnd_2931473 := by
    simpa [prefixWord, tailWord_2931473, baseEnd_2931473] using wordTrace_append hprefix tailTrace_2931473
  have hstable : (prefixWord ++ tailWord_2931473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931473).length < 2 ^ (prefixWord ++ tailWord_2931473).sum := by decide
  have hdescent : baseEnd_2931473 < baseStart_2931473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931474 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2931474 : Nat := 118140960795 + 2931474 * 2 ^ 59
def prefixEnd_2931474 : Nat := 4983230072969 + 3 ^ 40 * 2931474 * 2
def baseEnd_2931474 : Nat := 1505255188158368828193403

theorem tailTrace_2931474 : CollatzResearch.WordTrace tailWord_2931474 prefixEnd_2931474 1505255188158368828193403 := by
  unfold tailWord_2931474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26729910145444457186264369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71279760387851885830038317 26729910145444457186264369)
  ·
    refine ⟨20047432609083342889698277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26729910145444457186264369 20047432609083342889698277)
    ·
      refine ⟨3758893614203126791818427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20047432609083342889698277 3758893614203126791818427)
      ·
        refine ⟨5638340421304690187727641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758893614203126791818427 5638340421304690187727641)
        ·
          refine ⟨4228755315978517640795731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5638340421304690187727641 4228755315978517640795731)
          ·
            refine ⟨6343132973967776461193597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228755315978517640795731 6343132973967776461193597)
            ·
              refine ⟨2378674865237916172947599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6343132973967776461193597 2378674865237916172947599)
              ·
                refine ⟨3568012297856874259421399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378674865237916172947599 3568012297856874259421399)
                ·
                  refine ⟨5352018446785311389132099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568012297856874259421399 5352018446785311389132099)
                  ·
                    refine ⟨8028027670177967083698149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352018446785311389132099 8028027670177967083698149)
                    ·
                      refine ⟨1505255188158368828193403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8028027670177967083698149 1505255188158368828193403)
                      ·
                        rfl

theorem cell23_2931474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2931474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931474 prefixEnd_2931474 := by exact prefixLift 2931474
  have htrace : WordTrace (prefixWord ++ tailWord_2931474) baseStart_2931474 baseEnd_2931474 := by
    simpa [prefixWord, tailWord_2931474, baseEnd_2931474] using wordTrace_append hprefix tailTrace_2931474
  have hstable : (prefixWord ++ tailWord_2931474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931474).length < 2 ^ (prefixWord ++ tailWord_2931474).sum := by decide
  have hdescent : baseEnd_2931474 < baseStart_2931474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931483 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 7, 3, 2]
def baseStart_2931483 : Nat := 118140960795 + 2931483 * 2 ^ 59
def prefixEnd_2931483 : Nat := 4983230072969 + 3 ^ 40 * 2931483 * 2
def baseEnd_2931483 : Nat := 1505259809484259292980861

theorem tailTrace_2931483 : CollatzResearch.WordTrace tailWord_2931483 prefixEnd_2931483 1505259809484259292980861 := by
  unfold tailWord_2931483
  simp only [CollatzResearch.WordTrace]
  refine ⟨106919968838745223282135103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71279979225830148854756735 106919968838745223282135103)
  ·
    refine ⟨160379953258117834923202655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106919968838745223282135103 160379953258117834923202655)
    ·
      refine ⟨240569929887176752384803983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160379953258117834923202655 240569929887176752384803983)
      ·
        refine ⟨360854894830765128577205975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240569929887176752384803983 360854894830765128577205975)
        ·
          refine ⟨541282342246147692865808963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360854894830765128577205975 541282342246147692865808963)
          ·
            refine ⟨811923513369221539298713445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541282342246147692865808963 811923513369221539298713445)
            ·
              refine ⟨152235658756729038618508771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 811923513369221539298713445 152235658756729038618508771)
              ·
                refine ⟨228353488135093557927763157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152235658756729038618508771 228353488135093557927763157)
                ·
                  refine ⟨5352034878166255263931949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228353488135093557927763157 5352034878166255263931949)
                  ·
                    refine ⟨2007013079312345723974481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5352034878166255263931949 2007013079312345723974481)
                    ·
                      refine ⟨1505259809484259292980861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007013079312345723974481 1505259809484259292980861)
                      ·
                        rfl

theorem cell23_2931483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 3, 2].length) (baseStart_2931483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931483 prefixEnd_2931483 := by exact prefixLift 2931483
  have htrace : WordTrace (prefixWord ++ tailWord_2931483) baseStart_2931483 baseEnd_2931483 := by
    simpa [prefixWord, tailWord_2931483, baseEnd_2931483] using wordTrace_append hprefix tailTrace_2931483
  have hstable : (prefixWord ++ tailWord_2931483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931483).length < 2 ^ (prefixWord ++ tailWord_2931483).sum := by decide
  have hdescent : baseEnd_2931483 < baseStart_2931483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931543 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2931543 : Nat := 118140960795 + 2931543 * 2 ^ 59
def prefixEnd_2931543 : Nat := 4983230072969 + 3 ^ 40 * 2931543 * 2
def baseEnd_2931543 : Nat := 1505290618323529058230585

theorem tailTrace_2931543 : CollatzResearch.WordTrace tailWord_2931543 prefixEnd_2931543 1505290618323529058230585 := by
  unfold tailWord_2931543
  simp only [CollatzResearch.WordTrace]
  refine ⟨106922157218527853529319283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71281438145685235686212855 106922157218527853529319283)
  ·
    refine ⟨160383235827791780293978925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106922157218527853529319283 160383235827791780293978925)
    ·
      refine ⟨60143713435421917610242097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160383235827791780293978925 60143713435421917610242097)
      ·
        refine ⟨45107785076566438207681573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60143713435421917610242097 45107785076566438207681573)
        ·
          refine ⟨8457709701856207163940295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45107785076566438207681573 8457709701856207163940295)
          ·
            refine ⟨12686564552784310745910443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457709701856207163940295 12686564552784310745910443)
            ·
              refine ⟨19029846829176466118865665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686564552784310745910443 19029846829176466118865665)
              ·
                refine ⟨14272385121882349589149249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19029846829176466118865665 14272385121882349589149249)
                ·
                  refine ⟨10704288841411762191861937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14272385121882349589149249 10704288841411762191861937)
                  ·
                    refine ⟨8028216631058821643896453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10704288841411762191861937 8028216631058821643896453)
                    ·
                      refine ⟨1505290618323529058230585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8028216631058821643896453 1505290618323529058230585)
                      ·
                        rfl

theorem cell23_2931543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2931543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931543 prefixEnd_2931543 := by exact prefixLift 2931543
  have htrace : WordTrace (prefixWord ++ tailWord_2931543) baseStart_2931543 baseEnd_2931543 := by
    simpa [prefixWord, tailWord_2931543, baseEnd_2931543] using wordTrace_append hprefix tailTrace_2931543
  have hstable : (prefixWord ++ tailWord_2931543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931543).length < 2 ^ (prefixWord ++ tailWord_2931543).sum := by decide
  have hdescent : baseEnd_2931543 < baseStart_2931543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931563 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3]
def baseStart_2931563 : Nat := 118140960795 + 2931563 * 2 ^ 59
def prefixEnd_2931563 : Nat := 4983230072969 + 3 ^ 40 * 2931563 * 2
def baseEnd_2931563 : Nat := 1505300887936618979980493

theorem tailTrace_2931563 : CollatzResearch.WordTrace tailWord_2931563 prefixEnd_2931563 1505300887936618979980493 := by
  unfold tailWord_2931563
  simp only [CollatzResearch.WordTrace]
  refine ⟨106922886678455396945047343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71281924452303597963364895 106922886678455396945047343)
  ·
    refine ⟨160384330017683095417571015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106922886678455396945047343 160384330017683095417571015)
    ·
      refine ⟨240576495026524643126356523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160384330017683095417571015 240576495026524643126356523)
      ·
        refine ⟨360864742539786964689534785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240576495026524643126356523 360864742539786964689534785)
        ·
          refine ⟨270648556904840223517151089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360864742539786964689534785 270648556904840223517151089)
          ·
            refine ⟨202986417678630167637863317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270648556904840223517151089 202986417678630167637863317)
            ·
              refine ⟨9514988328685789108024843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202986417678630167637863317 9514988328685789108024843)
              ·
                refine ⟨14272482493028683662037265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514988328685789108024843 14272482493028683662037265)
                ·
                  refine ⟨10704361869771512746527949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14272482493028683662037265 10704361869771512746527949)
                  ·
                    refine ⟨4014135701164317279947981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10704361869771512746527949 4014135701164317279947981)
                    ·
                      refine ⟨1505300887936618979980493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014135701164317279947981 1505300887936618979980493)
                      ·
                        rfl

theorem cell23_2931563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].length) (baseStart_2931563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931563 prefixEnd_2931563 := by exact prefixLift 2931563
  have htrace : WordTrace (prefixWord ++ tailWord_2931563) baseStart_2931563 baseEnd_2931563 := by
    simpa [prefixWord, tailWord_2931563, baseEnd_2931563] using wordTrace_append hprefix tailTrace_2931563
  have hstable : (prefixWord ++ tailWord_2931563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931563).length < 2 ^ (prefixWord ++ tailWord_2931563).sum := by decide
  have hdescent : baseEnd_2931563 < baseStart_2931563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931564 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_2931564 : Nat := 118140960795 + 2931564 * 2 ^ 59
def prefixEnd_2931564 : Nat := 4983230072969 + 3 ^ 40 * 2931564 * 2
def baseEnd_2931564 : Nat := 1505301401417273476067989

theorem tailTrace_2931564 : CollatzResearch.WordTrace tailWord_2931564 prefixEnd_2931564 1505301401417273476067989 := by
  unfold tailWord_2931564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53461461575725887057916873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71281948767634516077222497 53461461575725887057916873)
  ·
    refine ⟨40096096181794415293437655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53461461575725887057916873 40096096181794415293437655)
    ·
      refine ⟨60144144272691622940156483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40096096181794415293437655 60144144272691622940156483)
      ·
        refine ⟨90216216409037434410234725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60144144272691622940156483 90216216409037434410234725)
        ·
          refine ⟨16915540576694518951919011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90216216409037434410234725 16915540576694518951919011)
          ·
            refine ⟨25373310865041778427878517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16915540576694518951919011 25373310865041778427878517)
            ·
              refine ⟨2378747893597666727613611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25373310865041778427878517 2378747893597666727613611)
              ·
                refine ⟨3568121840396500091420417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378747893597666727613611 3568121840396500091420417)
                ·
                  refine ⟨2676091380297375068565313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3568121840396500091420417 2676091380297375068565313)
                  ·
                    refine ⟨2007068535223031301423985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676091380297375068565313 2007068535223031301423985)
                    ·
                      refine ⟨1505301401417273476067989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007068535223031301423985 1505301401417273476067989)
                      ·
                        rfl

theorem cell23_2931564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_2931564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931564 prefixEnd_2931564 := by exact prefixLift 2931564
  have htrace : WordTrace (prefixWord ++ tailWord_2931564) baseStart_2931564 baseEnd_2931564 := by
    simpa [prefixWord, tailWord_2931564, baseEnd_2931564] using wordTrace_append hprefix tailTrace_2931564
  have hstable : (prefixWord ++ tailWord_2931564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931564).length < 2 ^ (prefixWord ++ tailWord_2931564).sum := by decide
  have hdescent : baseEnd_2931564 < baseStart_2931564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931576 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_2931576 : Nat := 118140960795 + 2931576 * 2 ^ 59
def prefixEnd_2931576 : Nat := 4983230072969 + 3 ^ 40 * 2931576 * 2
def baseEnd_2931576 : Nat := 1505307563185127429117933

theorem tailTrace_2931576 : CollatzResearch.WordTrace tailWord_2931576 prefixEnd_2931576 1505307563185127429117933 := by
  unfold tailWord_2931576
  simp only [CollatzResearch.WordTrace]
  refine ⟨53461680413704150082635291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71282240551605533443513721 53461680413704150082635291)
  ·
    refine ⟨80192520620556225123952937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53461680413704150082635291 80192520620556225123952937)
    ·
      refine ⟨60144390465417168842964703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80192520620556225123952937 60144390465417168842964703)
      ·
        refine ⟨90216585698125753264447055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60144390465417168842964703 90216585698125753264447055)
        ·
          refine ⟨135324878547188629896670583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90216585698125753264447055 135324878547188629896670583)
          ·
            refine ⟨202987317820782944845005875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135324878547188629896670583 202987317820782944845005875)
            ·
              refine ⟨304480976731174417267508813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202987317820782944845005875 304480976731174417267508813)
              ·
                refine ⟨114180366274190406475315805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304480976731174417267508813 114180366274190406475315805)
                ·
                  refine ⟨42817637352821402428243427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114180366274190406475315805 42817637352821402428243427)
                  ·
                    refine ⟨64226456029232103642365141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42817637352821402428243427 64226456029232103642365141)
                    ·
                      refine ⟨1505307563185127429117933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64226456029232103642365141 1505307563185127429117933)
                      ·
                        rfl

theorem cell23_2931576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_2931576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931576 prefixEnd_2931576 := by exact prefixLift 2931576
  have htrace : WordTrace (prefixWord ++ tailWord_2931576) baseStart_2931576 baseEnd_2931576 := by
    simpa [prefixWord, tailWord_2931576, baseEnd_2931576] using wordTrace_append hprefix tailTrace_2931576
  have hstable : (prefixWord ++ tailWord_2931576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931576).length < 2 ^ (prefixWord ++ tailWord_2931576).sum := by decide
  have hdescent : baseEnd_2931576 < baseStart_2931576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931610 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2931610 : Nat := 118140960795 + 2931610 * 2 ^ 59
def prefixEnd_2931610 : Nat := 4983230072969 + 3 ^ 40 * 2931610 * 2
def baseEnd_2931610 : Nat := 1505325021527380296092777

theorem tailTrace_2931610 : CollatzResearch.WordTrace tailWord_2931610 prefixEnd_2931610 1505325021527380296092777 := by
  unfold tailWord_2931610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26731150227321280993002071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71283067272856749314672189 26731150227321280993002071)
  ·
    refine ⟨40096725340981921489503107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26731150227321280993002071 40096725340981921489503107)
    ·
      refine ⟨60145088011472882234254661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40096725340981921489503107 60145088011472882234254661)
      ·
        refine ⟨11277204002151165418922749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60145088011472882234254661 11277204002151165418922749)
        ·
          refine ⟨4228951500806687032096031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11277204002151165418922749 4228951500806687032096031)
          ·
            refine ⟨6343427251210030548144047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228951500806687032096031 6343427251210030548144047)
            ·
              refine ⟨9515140876815045822216071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343427251210030548144047 9515140876815045822216071)
              ·
                refine ⟨14272711315222568733324107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515140876815045822216071 14272711315222568733324107)
                ·
                  refine ⟨21409066972833853099986161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14272711315222568733324107 21409066972833853099986161)
                  ·
                    refine ⟨16056800229625389824989621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21409066972833853099986161 16056800229625389824989621)
                    ·
                      refine ⟨1505325021527380296092777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16056800229625389824989621 1505325021527380296092777)
                      ·
                        rfl

theorem cell23_2931610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2931610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931610 prefixEnd_2931610 := by exact prefixLift 2931610
  have htrace : WordTrace (prefixWord ++ tailWord_2931610) baseStart_2931610 baseEnd_2931610 := by
    simpa [prefixWord, tailWord_2931610, baseEnd_2931610] using wordTrace_append hprefix tailTrace_2931610
  have hstable : (prefixWord ++ tailWord_2931610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931610).length < 2 ^ (prefixWord ++ tailWord_2931610).sum := by decide
  have hdescent : baseEnd_2931610 < baseStart_2931610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931620 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_2931620 : Nat := 118140960795 + 2931620 * 2 ^ 59
def prefixEnd_2931620 : Nat := 4983230072969 + 3 ^ 40 * 2931620 * 2
def baseEnd_2931620 : Nat := 1505330156333925256967731

theorem tailTrace_2931620 : CollatzResearch.WordTrace tailWord_2931620 prefixEnd_2931620 1505330156333925256967731 := by
  unfold tailWord_2931620
  simp only [CollatzResearch.WordTrace]
  refine ⟨53462482819624447839936157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71283310426165930453248209 53462482819624447839936157)
  ·
    refine ⟨20048431057359167939976059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53462482819624447839936157 20048431057359167939976059)
    ·
      refine ⟨30072646586038751909964089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20048431057359167939976059 30072646586038751909964089)
      ·
        refine ⟨22554484939529063932473067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30072646586038751909964089 22554484939529063932473067)
        ·
          refine ⟨33831727409293595898709601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22554484939529063932473067 33831727409293595898709601)
          ·
            refine ⟨25373795556970196924032201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33831727409293595898709601 25373795556970196924032201)
            ·
              refine ⟨19030346667727647693024151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25373795556970196924032201 19030346667727647693024151)
              ·
                refine ⟨28545520001591471539536227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19030346667727647693024151 28545520001591471539536227)
                ·
                  refine ⟨42818280002387207309304341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28545520001591471539536227 42818280002387207309304341)
                  ·
                    refine ⟨2007106875111900342623641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42818280002387207309304341 2007106875111900342623641)
                    ·
                      refine ⟨1505330156333925256967731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007106875111900342623641 1505330156333925256967731)
                      ·
                        rfl

theorem cell23_2931620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_2931620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931620 prefixEnd_2931620 := by exact prefixLift 2931620
  have htrace : WordTrace (prefixWord ++ tailWord_2931620) baseStart_2931620 baseEnd_2931620 := by
    simpa [prefixWord, tailWord_2931620, baseEnd_2931620] using wordTrace_append hprefix tailTrace_2931620
  have hstable : (prefixWord ++ tailWord_2931620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931620).length < 2 ^ (prefixWord ++ tailWord_2931620).sum := by decide
  have hdescent : baseEnd_2931620 < baseStart_2931620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931640 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_2931640 : Nat := 118140960795 + 2931640 * 2 ^ 59
def prefixEnd_2931640 : Nat := 4983230072969 + 3 ^ 40 * 2931640 * 2
def baseEnd_2931640 : Nat := 1505340425947015178717639

theorem tailTrace_2931640 : CollatzResearch.WordTrace tailWord_2931640 prefixEnd_2931640 1505340425947015178717639 := by
  unfold tailWord_2931640
  simp only [CollatzResearch.WordTrace]
  refine ⟨53462847549588219547800187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71283796732784292730400249 53462847549588219547800187)
  ·
    refine ⟨80194271324382329321700281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53462847549588219547800187 80194271324382329321700281)
    ·
      refine ⟨60145703493286746991275211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80194271324382329321700281 60145703493286746991275211)
      ·
        refine ⟨90218555239930120486912817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60145703493286746991275211 90218555239930120486912817)
        ·
          refine ⟨67663916429947590365184613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90218555239930120486912817 67663916429947590365184613)
          ·
            refine ⟨12686984330615173193472115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67663916429947590365184613 12686984330615173193472115)
            ·
              refine ⟨19030476495922759790208173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686984330615173193472115 19030476495922759790208173)
              ·
                refine ⟨7136428685971034921328065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19030476495922759790208173 7136428685971034921328065)
                ·
                  refine ⟨5352321514478276190996049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7136428685971034921328065 5352321514478276190996049)
                  ·
                    refine ⟨4014241135858707143247037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352321514478276190996049 4014241135858707143247037)
                    ·
                      refine ⟨1505340425947015178717639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014241135858707143247037 1505340425947015178717639)
                      ·
                        rfl

theorem cell23_2931640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_2931640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931640 prefixEnd_2931640 := by exact prefixLift 2931640
  have htrace : WordTrace (prefixWord ++ tailWord_2931640) baseStart_2931640 baseEnd_2931640 := by
    simpa [prefixWord, tailWord_2931640, baseEnd_2931640] using wordTrace_append hprefix tailTrace_2931640
  have hstable : (prefixWord ++ tailWord_2931640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931640).length < 2 ^ (prefixWord ++ tailWord_2931640).sum := by decide
  have hdescent : baseEnd_2931640 < baseStart_2931640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931653 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_2931653 : Nat := 118140960795 + 2931653 * 2 ^ 59
def prefixEnd_2931653 : Nat := 4983230072969 + 3 ^ 40 * 2931653 * 2
def baseEnd_2931653 : Nat := 1505347101195523627855079

theorem tailTrace_2931653 : CollatzResearch.WordTrace tailWord_2931653 prefixEnd_2931653 1505347101195523627855079 := by
  unfold tailWord_2931653
  simp only [CollatzResearch.WordTrace]
  refine ⟨106926169248129342315823613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71284112832086228210549075 106926169248129342315823613)
  ·
    refine ⟨40097313468048503368433855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106926169248129342315823613 40097313468048503368433855)
    ·
      refine ⟨60145970202072755052650783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40097313468048503368433855 60145970202072755052650783)
      ·
        refine ⟨90218955303109132578976175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60145970202072755052650783 90218955303109132578976175)
        ·
          refine ⟨135328432954663698868464263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90218955303109132578976175 135328432954663698868464263)
          ·
            refine ⟨202992649431995548302696395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135328432954663698868464263 202992649431995548302696395)
            ·
              refine ⟨304488974147993322454044593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202992649431995548302696395 304488974147993322454044593)
              ·
                refine ⟨228366730610994991840533445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304488974147993322454044593 228366730610994991840533445)
                ·
                  refine ⟨42818761989561560970100021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228366730610994991840533445 42818761989561560970100021)
                  ·
                    refine ⟨4014258936521396340946877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42818761989561560970100021 4014258936521396340946877)
                    ·
                      refine ⟨1505347101195523627855079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014258936521396340946877 1505347101195523627855079)
                      ·
                        rfl

theorem cell23_2931653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_2931653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931653 prefixEnd_2931653 := by exact prefixLift 2931653
  have htrace : WordTrace (prefixWord ++ tailWord_2931653) baseStart_2931653 baseEnd_2931653 := by
    simpa [prefixWord, tailWord_2931653, baseEnd_2931653] using wordTrace_append hprefix tailTrace_2931653
  have hstable : (prefixWord ++ tailWord_2931653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931653).length < 2 ^ (prefixWord ++ tailWord_2931653).sum := by decide
  have hdescent : baseEnd_2931653 < baseStart_2931653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931660 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 6]
def baseStart_2931660 : Nat := 118140960795 + 2931660 * 2 ^ 59
def prefixEnd_2931660 : Nat := 4983230072969 + 3 ^ 40 * 2931660 * 2
def baseEnd_2931660 : Nat := 167261188395567233385283

theorem tailTrace_2931660 : CollatzResearch.WordTrace tailWord_2931660 prefixEnd_2931660 167261188395567233385283 := by
  unfold tailWord_2931660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53463212279551991255664217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71284283039402655007552289 53463212279551991255664217)
  ·
    refine ⟨40097409209663993441748163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53463212279551991255664217 40097409209663993441748163)
    ·
      refine ⟨60146113814495990162622245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40097409209663993441748163 60146113814495990162622245)
      ·
        refine ⟨11277396340217998155491671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60146113814495990162622245 11277396340217998155491671)
        ·
          refine ⟨16916094510326997233237507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11277396340217998155491671 16916094510326997233237507)
          ·
            refine ⟨25374141765490495849856261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16916094510326997233237507 25374141765490495849856261)
            ·
              refine ⟨4757651581029467971848049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25374141765490495849856261 4757651581029467971848049)
              ·
                refine ⟨3568238685772100978886037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757651581029467971848049 3568238685772100978886037)
                ·
                  refine ⟨167261188395567233385283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3568238685772100978886037 167261188395567233385283)
                  ·
                    rfl

theorem cell23_2931660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_2931660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931660 prefixEnd_2931660 := by exact prefixLift 2931660
  have htrace : WordTrace (prefixWord ++ tailWord_2931660) baseStart_2931660 baseEnd_2931660 := by
    simpa [prefixWord, tailWord_2931660, baseEnd_2931660] using wordTrace_append hprefix tailTrace_2931660
  have hstable : (prefixWord ++ tailWord_2931660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931660).length < 2 ^ (prefixWord ++ tailWord_2931660).sum := by decide
  have hdescent : baseEnd_2931660 < baseStart_2931660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931683 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2931683 : Nat := 118140960795 + 2931683 * 2 ^ 59
def prefixEnd_2931683 : Nat := 4983230072969 + 3 ^ 40 * 2931683 * 2
def baseEnd_2931683 : Nat := 1505362505615158510479941

theorem tailTrace_2931683 : CollatzResearch.WordTrace tailWord_2931683 prefixEnd_2931683 1505362505615158510479941 := by
  unfold tailWord_2931683
  simp only [CollatzResearch.WordTrace]
  refine ⟨106927263438020657439415703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71284842292013771626277135 106927263438020657439415703)
  ·
    refine ⟨160390895157030986159123555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106927263438020657439415703 160390895157030986159123555)
    ·
      refine ⟨240586342735546479238685333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160390895157030986159123555 240586342735546479238685333)
      ·
        refine ⟨11277484815728741214313375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240586342735546479238685333 11277484815728741214313375)
        ·
          refine ⟨16916227223593111821470063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11277484815728741214313375 16916227223593111821470063)
          ·
            refine ⟨25374340835389667732205095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16916227223593111821470063 25374340835389667732205095)
            ·
              refine ⟨38061511253084501598307643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25374340835389667732205095 38061511253084501598307643)
              ·
                refine ⟨57092266879626752397461465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38061511253084501598307643 57092266879626752397461465)
                ·
                  refine ⟨42819200159720064298096099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57092266879626752397461465 42819200159720064298096099)
                  ·
                    refine ⟨64228800239580096447144149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42819200159720064298096099 64228800239580096447144149)
                    ·
                      refine ⟨1505362505615158510479941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64228800239580096447144149 1505362505615158510479941)
                      ·
                        rfl

theorem cell23_2931683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2931683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931683 prefixEnd_2931683 := by exact prefixLift 2931683
  have htrace : WordTrace (prefixWord ++ tailWord_2931683) baseStart_2931683 baseEnd_2931683 := by
    simpa [prefixWord, tailWord_2931683, baseEnd_2931683] using wordTrace_append hprefix tailTrace_2931683
  have hstable : (prefixWord ++ tailWord_2931683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931683).length < 2 ^ (prefixWord ++ tailWord_2931683).sum := by decide
  have hdescent : baseEnd_2931683 < baseStart_2931683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931687 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2931687 : Nat := 118140960795 + 2931687 * 2 ^ 59
def prefixEnd_2931687 : Nat := 4983230072969 + 3 ^ 40 * 2931687 * 2
def baseEnd_2931687 : Nat := 1505364559537776494829923

theorem tailTrace_2931687 : CollatzResearch.WordTrace tailWord_2931687 prefixEnd_2931687 1505364559537776494829923 := by
  unfold tailWord_2931687
  simp only [CollatzResearch.WordTrace]
  refine ⟨106927409330006166122561315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71284939553337444081707543 106927409330006166122561315)
  ·
    refine ⟨160391113995009249183841973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106927409330006166122561315 160391113995009249183841973)
    ·
      refine ⟨15036666937032117110985185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160391113995009249183841973 15036666937032117110985185)
      ·
        refine ⟨11277500202774087833238889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15036666937032117110985185 11277500202774087833238889)
        ·
          refine ⟨8458125152080565874929167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277500202774087833238889 8458125152080565874929167)
          ·
            refine ⟨12687187728120848812393751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458125152080565874929167 12687187728120848812393751)
            ·
              refine ⟨19030781592181273218590627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687187728120848812393751 19030781592181273218590627)
              ·
                refine ⟨28546172388271909827885941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19030781592181273218590627 28546172388271909827885941)
                ·
                  refine ⟨2676203661400491546364307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28546172388271909827885941 2676203661400491546364307)
                  ·
                    refine ⟨4014305492100737319546461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676203661400491546364307 4014305492100737319546461)
                    ·
                      refine ⟨1505364559537776494829923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014305492100737319546461 1505364559537776494829923)
                      ·
                        rfl

theorem cell23_2931687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2931687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931687 prefixEnd_2931687 := by exact prefixLift 2931687
  have htrace : WordTrace (prefixWord ++ tailWord_2931687) baseStart_2931687 baseEnd_2931687 := by
    simpa [prefixWord, tailWord_2931687, baseEnd_2931687] using wordTrace_append hprefix tailTrace_2931687
  have hstable : (prefixWord ++ tailWord_2931687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931687).length < 2 ^ (prefixWord ++ tailWord_2931687).sum := by decide
  have hdescent : baseEnd_2931687 < baseStart_2931687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931690 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2931690 : Nat := 118140960795 + 2931690 * 2 ^ 59
def prefixEnd_2931690 : Nat := 4983230072969 + 3 ^ 40 * 2931690 * 2
def baseEnd_2931690 : Nat := 501788699993246661030803

theorem tailTrace_2931690 : CollatzResearch.WordTrace tailWord_2931690 prefixEnd_2931690 501788699993246661030803 := by
  unfold tailWord_2931690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26731879687248824408730131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71285012499330198423280349 26731879687248824408730131)
  ·
    refine ⟨40097819530873236613095197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26731879687248824408730131 40097819530873236613095197)
    ·
      refine ⟨15036682324077463729910699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40097819530873236613095197 15036682324077463729910699)
      ·
        refine ⟨22555023486116195594866049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15036682324077463729910699 22555023486116195594866049)
        ·
          refine ⟨16916267614587146696149537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22555023486116195594866049 16916267614587146696149537)
          ·
            refine ⟨12687200710940360022112153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16916267614587146696149537 12687200710940360022112153)
            ·
              refine ⟨9515400533205270016584115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12687200710940360022112153 9515400533205270016584115)
              ·
                refine ⟨14273100799807905024876173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515400533205270016584115 14273100799807905024876173)
                ·
                  refine ⟨5352412799927964384328565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14273100799807905024876173 5352412799927964384328565)
                  ·
                    refine ⟨501788699993246661030803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5352412799927964384328565 501788699993246661030803)
                    ·
                      rfl

theorem cell23_2931690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2931690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931690 prefixEnd_2931690 := by exact prefixLift 2931690
  have htrace : WordTrace (prefixWord ++ tailWord_2931690) baseStart_2931690 baseEnd_2931690 := by
    simpa [prefixWord, tailWord_2931690, baseEnd_2931690] using wordTrace_append hprefix tailTrace_2931690
  have hstable : (prefixWord ++ tailWord_2931690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931690).length < 2 ^ (prefixWord ++ tailWord_2931690).sum := by decide
  have hdescent : baseEnd_2931690 < baseStart_2931690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931697 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_2931697 : Nat := 118140960795 + 2931697 * 2 ^ 59
def prefixEnd_2931697 : Nat := 4983230072969 + 3 ^ 40 * 2931697 * 2
def baseEnd_2931697 : Nat := 1505369694344321455704877

theorem tailTrace_2931697 : CollatzResearch.WordTrace tailWord_2931697 prefixEnd_2931697 1505369694344321455704877 := by
  unfold tailWord_2931697
  simp only [CollatzResearch.WordTrace]
  refine ⟨106927774059969937830425345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71285182706646625220283563 106927774059969937830425345)
  ·
    refine ⟨80195830544977453372819009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106927774059969937830425345 80195830544977453372819009)
    ·
      refine ⟨60146872908733090029614257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80195830544977453372819009 60146872908733090029614257)
      ·
        refine ⟨45110154681549817522210693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60146872908733090029614257 45110154681549817522210693)
        ·
          refine ⟨8458154002790590785414505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45110154681549817522210693 8458154002790590785414505)
          ·
            refine ⟨6343615502092943089060879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8458154002790590785414505 6343615502092943089060879)
            ·
              refine ⟨9515423253139414633591319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343615502092943089060879 9515423253139414633591319)
              ·
                refine ⟨14273134879709121950386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515423253139414633591319 14273134879709121950386979)
                ·
                  refine ⟨21409702319563682925580469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14273134879709121950386979 21409702319563682925580469)
                  ·
                    refine ⟨2007159592459095274273169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21409702319563682925580469 2007159592459095274273169)
                    ·
                      refine ⟨1505369694344321455704877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007159592459095274273169 1505369694344321455704877)
                      ·
                        rfl

theorem cell23_2931697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_2931697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931697 prefixEnd_2931697 := by exact prefixLift 2931697
  have htrace : WordTrace (prefixWord ++ tailWord_2931697) baseStart_2931697 baseEnd_2931697 := by
    simpa [prefixWord, tailWord_2931697, baseEnd_2931697] using wordTrace_append hprefix tailTrace_2931697
  have hstable : (prefixWord ++ tailWord_2931697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931697).length < 2 ^ (prefixWord ++ tailWord_2931697).sum := by decide
  have hdescent : baseEnd_2931697 < baseStart_2931697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931747 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 3]
def baseStart_2931747 : Nat := 118140960795 + 2931747 * 2 ^ 59
def prefixEnd_2931747 : Nat := 4983230072969 + 3 ^ 40 * 2931747 * 2
def baseEnd_2931747 : Nat := 1505395368377046260079647

theorem tailTrace_2931747 : CollatzResearch.WordTrace tailWord_2931747 prefixEnd_2931747 1505395368377046260079647 := by
  unfold tailWord_2931747
  simp only [CollatzResearch.WordTrace]
  refine ⟨106929597709788796369745495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71286398473192530913163663 106929597709788796369745495)
  ·
    refine ⟨160394396564683194554618243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106929597709788796369745495 160394396564683194554618243)
    ·
      refine ⟨240591594847024791831927365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160394396564683194554618243 240591594847024791831927365)
      ·
        refine ⟨45110924033817148468486381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240591594847024791831927365 45110924033817148468486381)
        ·
          refine ⟨16916596512681430675682393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45110924033817148468486381 16916596512681430675682393)
          ·
            refine ⟨12687447384511073006761795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16916596512681430675682393 12687447384511073006761795)
            ·
              refine ⟨19031171076766609510142693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687447384511073006761795 19031171076766609510142693)
              ·
                refine ⟨3568344576893739283151755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19031171076766609510142693 3568344576893739283151755)
                ·
                  refine ⟨5352516865340608924727633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568344576893739283151755 5352516865340608924727633)
                  ·
                    refine ⟨4014387649005456693545725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352516865340608924727633 4014387649005456693545725)
                    ·
                      refine ⟨1505395368377046260079647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014387649005456693545725 1505395368377046260079647)
                      ·
                        rfl

theorem cell23_2931747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_2931747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931747 prefixEnd_2931747 := by exact prefixLift 2931747
  have htrace : WordTrace (prefixWord ++ tailWord_2931747) baseStart_2931747 baseEnd_2931747 := by
    simpa [prefixWord, tailWord_2931747, baseEnd_2931747] using wordTrace_append hprefix tailTrace_2931747
  have hstable : (prefixWord ++ tailWord_2931747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931747).length < 2 ^ (prefixWord ++ tailWord_2931747).sum := by decide
  have hdescent : baseEnd_2931747 < baseStart_2931747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931760 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_2931760 : Nat := 118140960795 + 2931760 * 2 ^ 59
def prefixEnd_2931760 : Nat := 4983230072969 + 3 ^ 40 * 2931760 * 2
def baseEnd_2931760 : Nat := 1505402043625554709217087

theorem tailTrace_2931760 : CollatzResearch.WordTrace tailWord_2931760 prefixEnd_2931760 1505402043625554709217087 := by
  unfold tailWord_2931760
  simp only [CollatzResearch.WordTrace]
  refine ⟨53465035929370849794984367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71286714572494466393312489 53465035929370849794984367)
  ·
    refine ⟨80197553894056274692476551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53465035929370849794984367 80197553894056274692476551)
    ·
      refine ⟨120296330841084412038714827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80197553894056274692476551 120296330841084412038714827)
      ·
        refine ⟨180444496261626618058072241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120296330841084412038714827 180444496261626618058072241)
        ·
          refine ⟨135333372196219963543554181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180444496261626618058072241 135333372196219963543554181)
          ·
            refine ⟨25375007286791243164416409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135333372196219963543554181 25375007286791243164416409)
            ·
              refine ⟨19031255465093432373312307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25375007286791243164416409 19031255465093432373312307)
              ·
                refine ⟨28546883197640148559968461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19031255465093432373312307 28546883197640148559968461)
                ·
                  refine ⟨10705081199115055709988173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28546883197640148559968461 10705081199115055709988173)
                  ·
                    refine ⟨4014405449668145891245565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10705081199115055709988173 4014405449668145891245565)
                    ·
                      refine ⟨1505402043625554709217087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014405449668145891245565 1505402043625554709217087)
                      ·
                        rfl

theorem cell23_2931760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_2931760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931760 prefixEnd_2931760 := by exact prefixLift 2931760
  have htrace : WordTrace (prefixWord ++ tailWord_2931760) baseStart_2931760 baseEnd_2931760 := by
    simpa [prefixWord, tailWord_2931760, baseEnd_2931760] using wordTrace_append hprefix tailTrace_2931760
  have hstable : (prefixWord ++ tailWord_2931760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931760).length < 2 ^ (prefixWord ++ tailWord_2931760).sum := by decide
  have hdescent : baseEnd_2931760 < baseStart_2931760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931763 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 1, 9]
def baseStart_2931763 : Nat := 118140960795 + 2931763 * 2 ^ 59
def prefixEnd_2931763 : Nat := 4983230072969 + 3 ^ 40 * 2931763 * 2
def baseEnd_2931763 : Nat := 501801194689172732493191

theorem tailTrace_2931763 : CollatzResearch.WordTrace tailWord_2931763 prefixEnd_2931763 501801194689172732493191 := by
  unfold tailWord_2931763
  simp only [CollatzResearch.WordTrace]
  refine ⟨106930181277730831102327943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71286787518487220734885295 106930181277730831102327943)
  ·
    refine ⟨160395271916596246653491915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106930181277730831102327943 160395271916596246653491915)
    ·
      refine ⟨240592907874894369980237873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160395271916596246653491915 240592907874894369980237873)
      ·
        refine ⟨180444680906170777485178405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240592907874894369980237873 180444680906170777485178405)
        ·
          refine ⟨33833377669907020778470951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180444680906170777485178405 33833377669907020778470951)
          ·
            refine ⟨50750066504860531167706427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33833377669907020778470951 50750066504860531167706427)
            ·
              refine ⟨76125099757290796751559641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50750066504860531167706427 76125099757290796751559641)
              ·
                refine ⟨57093824817968097563669731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76125099757290796751559641 57093824817968097563669731)
                ·
                  refine ⟨85640737226952146345504597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57093824817968097563669731 85640737226952146345504597)
                  ·
                    refine ⟨501801194689172732493191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85640737226952146345504597 501801194689172732493191)
                    ·
                      rfl

theorem cell23_2931763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_2931763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931763 prefixEnd_2931763 := by exact prefixLift 2931763
  have htrace : WordTrace (prefixWord ++ tailWord_2931763) baseStart_2931763 baseEnd_2931763 := by
    simpa [prefixWord, tailWord_2931763, baseEnd_2931763] using wordTrace_append hprefix tailTrace_2931763
  have hstable : (prefixWord ++ tailWord_2931763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931763).length < 2 ^ (prefixWord ++ tailWord_2931763).sum := by decide
  have hdescent : baseEnd_2931763 < baseStart_2931763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931764 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2931764 : Nat := 118140960795 + 2931764 * 2 ^ 59
def prefixEnd_2931764 : Nat := 4983230072969 + 3 ^ 40 * 2931764 * 2
def baseEnd_2931764 : Nat := 1505404097548172693567069

theorem tailTrace_2931764 : CollatzResearch.WordTrace tailWord_2931764 prefixEnd_2931764 1505404097548172693567069 := by
  unfold tailWord_2931764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53465108875363604136557173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71286811833818138848742897 53465108875363604136557173)
  ·
    refine ⟨5012353957065337887802235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53465108875363604136557173 5012353957065337887802235)
    ·
      refine ⟨7518530935598006831703353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5012353957065337887802235 7518530935598006831703353)
      ·
        refine ⟨5638898201698505123777515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7518530935598006831703353 5638898201698505123777515)
        ·
          refine ⟨8458347302547757685666273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638898201698505123777515 8458347302547757685666273)
          ·
            refine ⟨6343760476910818264249705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8458347302547757685666273 6343760476910818264249705)
            ·
              refine ⟨4757820357683113698187279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343760476910818264249705 4757820357683113698187279)
              ·
                refine ⟨7136730536524670547280919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757820357683113698187279 7136730536524670547280919)
                ·
                  refine ⟨10705095804787005820921379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136730536524670547280919 10705095804787005820921379)
                  ·
                    refine ⟨16057643707180508731382069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10705095804787005820921379 16057643707180508731382069)
                    ·
                      refine ⟨1505404097548172693567069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16057643707180508731382069 1505404097548172693567069)
                      ·
                        rfl

theorem cell23_2931764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2931764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931764 prefixEnd_2931764 := by exact prefixLift 2931764
  have htrace : WordTrace (prefixWord ++ tailWord_2931764) baseStart_2931764 baseEnd_2931764 := by
    simpa [prefixWord, tailWord_2931764, baseEnd_2931764] using wordTrace_append hprefix tailTrace_2931764
  have hstable : (prefixWord ++ tailWord_2931764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931764).length < 2 ^ (prefixWord ++ tailWord_2931764).sum := by decide
  have hdescent : baseEnd_2931764 < baseStart_2931764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931804 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2931804 : Nat := 118140960795 + 2931804 * 2 ^ 59
def prefixEnd_2931804 : Nat := 4983230072969 + 3 ^ 40 * 2931804 * 2
def baseEnd_2931804 : Nat := 1505424636774352537066885

theorem tailTrace_2931804 : CollatzResearch.WordTrace tailWord_2931804 prefixEnd_2931804 1505424636774352537066885 := by
  unfold tailWord_2931804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53465838335291147552285233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71287784447054863403046977 53465838335291147552285233)
  ·
    refine ⟨40099378751468360664213925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53465838335291147552285233 40099378751468360664213925)
    ·
      refine ⟨7518633515900317624540111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40099378751468360664213925 7518633515900317624540111)
      ·
        refine ⟨11277950273850476436810167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518633515900317624540111 11277950273850476436810167)
        ·
          refine ⟨16916925410775714655215251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11277950273850476436810167 16916925410775714655215251)
          ·
            refine ⟨25375388116163571982822877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16916925410775714655215251 25375388116163571982822877)
            ·
              refine ⟨9515770543561339493558579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25375388116163571982822877 9515770543561339493558579)
              ·
                refine ⟨14273655815342009240337869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515770543561339493558579 14273655815342009240337869)
                ·
                  refine ⟨5352620930753253465126701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14273655815342009240337869 5352620930753253465126701)
                  ·
                    refine ⟨2007232849032470049422513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5352620930753253465126701 2007232849032470049422513)
                    ·
                      refine ⟨1505424636774352537066885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007232849032470049422513 1505424636774352537066885)
                      ·
                        rfl

theorem cell23_2931804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2931804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931804 prefixEnd_2931804 := by exact prefixLift 2931804
  have htrace : WordTrace (prefixWord ++ tailWord_2931804) baseStart_2931804 baseEnd_2931804 := by
    simpa [prefixWord, tailWord_2931804, baseEnd_2931804] using wordTrace_append hprefix tailTrace_2931804
  have hstable : (prefixWord ++ tailWord_2931804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931804).length < 2 ^ (prefixWord ++ tailWord_2931804).sum := by decide
  have hdescent : baseEnd_2931804 < baseStart_2931804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931817 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 4, 2]
def baseStart_2931817 : Nat := 118140960795 + 2931817 * 2 ^ 59
def prefixEnd_2931817 : Nat := 4983230072969 + 3 ^ 40 * 2931817 * 2
def baseEnd_2931817 : Nat := 1505431312022860986204325

theorem tailTrace_2931817 : CollatzResearch.WordTrace tailWord_2931817 prefixEnd_2931817 1505431312022860986204325 := by
  unfold tailWord_2931817
  simp only [CollatzResearch.WordTrace]
  refine ⟨106932150819535198324793705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71288100546356798883195803 106932150819535198324793705)
  ·
    refine ⟨80199113114651398743595279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106932150819535198324793705 80199113114651398743595279)
    ·
      refine ⟨120298669671977098115392919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80199113114651398743595279 120298669671977098115392919)
      ·
        refine ⟨180448004507965647173089379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120298669671977098115392919 180448004507965647173089379)
        ·
          refine ⟨270672006761948470759634069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180448004507965647173089379 270672006761948470759634069)
          ·
            refine ⟨12687750316966334566857847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270672006761948470759634069 12687750316966334566857847)
            ·
              refine ⟨19031625475449501850286771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687750316966334566857847 19031625475449501850286771)
              ·
                refine ⟨28547438213174252775430157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19031625475449501850286771 28547438213174252775430157)
                ·
                  refine ⟨10705289329940344790786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28547438213174252775430157 10705289329940344790786309)
                  ·
                    refine ⟨2007241749363814648272433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10705289329940344790786309 2007241749363814648272433)
                    ·
                      refine ⟨1505431312022860986204325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007241749363814648272433 1505431312022860986204325)
                      ·
                        rfl

theorem cell23_2931817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4, 2].length) (baseStart_2931817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931817 prefixEnd_2931817 := by exact prefixLift 2931817
  have htrace : WordTrace (prefixWord ++ tailWord_2931817) baseStart_2931817 baseEnd_2931817 := by
    simpa [prefixWord, tailWord_2931817, baseEnd_2931817] using wordTrace_append hprefix tailTrace_2931817
  have hstable : (prefixWord ++ tailWord_2931817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931817).length < 2 ^ (prefixWord ++ tailWord_2931817).sum := by decide
  have hdescent : baseEnd_2931817 < baseStart_2931817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931820 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2931820 : Nat := 118140960795 + 2931820 * 2 ^ 59
def prefixEnd_2931820 : Nat := 4983230072969 + 3 ^ 40 * 2931820 * 2
def baseEnd_2931820 : Nat := 1505432852464824474466811

theorem tailTrace_2931820 : CollatzResearch.WordTrace tailWord_2931820 prefixEnd_2931820 1505432852464824474466811 := by
  unfold tailWord_2931820
  simp only [CollatzResearch.WordTrace]
  refine ⟨53466130119262164918576457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71288173492349553224768609 53466130119262164918576457)
  ·
    refine ⟨40099597589446623688932343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53466130119262164918576457 40099597589446623688932343)
    ·
      refine ⟨60149396384169935533398515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40099597589446623688932343 60149396384169935533398515)
      ·
        refine ⟨90224094576254903300097773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60149396384169935533398515 90224094576254903300097773)
        ·
          refine ⟨33834035466095588737536665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90224094576254903300097773 33834035466095588737536665)
          ·
            refine ⟨25375526599571691553152499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33834035466095588737536665 25375526599571691553152499)
            ·
              refine ⟨38063289899357537329728749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25375526599571691553152499 38063289899357537329728749)
              ·
                refine ⟨14273733712259076498648281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38063289899357537329728749 14273733712259076498648281)
                ·
                  refine ⟨10705300284194307373986211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14273733712259076498648281 10705300284194307373986211)
                  ·
                    refine ⟨16057950426291461060979317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10705300284194307373986211 16057950426291461060979317)
                    ·
                      refine ⟨1505432852464824474466811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16057950426291461060979317 1505432852464824474466811)
                      ·
                        rfl

theorem cell23_2931820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2931820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931820 prefixEnd_2931820 := by exact prefixLift 2931820
  have htrace : WordTrace (prefixWord ++ tailWord_2931820) baseStart_2931820 baseEnd_2931820 := by
    simpa [prefixWord, tailWord_2931820, baseEnd_2931820] using wordTrace_append hprefix tailTrace_2931820
  have hstable : (prefixWord ++ tailWord_2931820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931820).length < 2 ^ (prefixWord ++ tailWord_2931820).sum := by decide
  have hdescent : baseEnd_2931820 < baseStart_2931820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931829 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2931829 : Nat := 118140960795 + 2931829 * 2 ^ 59
def prefixEnd_2931829 : Nat := 4983230072969 + 3 ^ 40 * 2931829 * 2
def baseEnd_2931829 : Nat := 1505437473790714939254271

theorem tailTrace_2931829 : CollatzResearch.WordTrace tailWord_2931829 prefixEnd_2931829 1505437473790714939254271 := by
  unfold tailWord_2931829
  simp only [CollatzResearch.WordTrace]
  refine ⟨106932588495491724374230541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71288392330327816249487027 106932588495491724374230541)
  ·
    refine ⟨40099720685809396640336453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106932588495491724374230541 40099720685809396640336453)
    ·
      refine ⟨7518697628589261870063085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40099720685809396640336453 7518697628589261870063085)
      ·
        refine ⟨2819511610720973201273657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7518697628589261870063085 2819511610720973201273657)
        ·
          refine ⟨2114633708040729900955243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2819511610720973201273657 2114633708040729900955243)
          ·
            refine ⟨3171950562061094851432865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114633708040729900955243 3171950562061094851432865)
            ·
              refine ⟨2378962921545821138574649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171950562061094851432865 2378962921545821138574649)
              ·
                refine ⟨1784222191159365853930987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378962921545821138574649 1784222191159365853930987)
                ·
                  refine ⟨2676333286739048780896481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784222191159365853930987 2676333286739048780896481)
                  ·
                    refine ⟨2007249965054286585672361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676333286739048780896481 2007249965054286585672361)
                    ·
                      refine ⟨1505437473790714939254271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007249965054286585672361 1505437473790714939254271)
                      ·
                        rfl

theorem cell23_2931829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2931829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931829 prefixEnd_2931829 := by exact prefixLift 2931829
  have htrace : WordTrace (prefixWord ++ tailWord_2931829) baseStart_2931829 baseEnd_2931829 := by
    simpa [prefixWord, tailWord_2931829, baseEnd_2931829] using wordTrace_append hprefix tailTrace_2931829
  have hstable : (prefixWord ++ tailWord_2931829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931829).length < 2 ^ (prefixWord ++ tailWord_2931829).sum := by decide
  have hdescent : baseEnd_2931829 < baseStart_2931829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931885 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_2931885 : Nat := 118140960795 + 2931885 * 2 ^ 59
def prefixEnd_2931885 : Nat := 4983230072969 + 3 ^ 40 * 2931885 * 2
def baseEnd_2931885 : Nat := 1505466228707366720154013

theorem tailTrace_2931885 : CollatzResearch.WordTrace tailWord_2931885 prefixEnd_2931885 1505466228707366720154013 := by
  unfold tailWord_2931885
  simp only [CollatzResearch.WordTrace]
  refine ⟨106934630983288845938269109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71289753988859230625512739 106934630983288845938269109)
  ·
    refine ⟨10025121654683329306712729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106934630983288845938269109 10025121654683329306712729)
    ·
      refine ⟨7518841241012496980034547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10025121654683329306712729 7518841241012496980034547)
      ·
        refine ⟨11278261861518745470051821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518841241012496980034547 11278261861518745470051821)
        ·
          refine ⟨4229348198069529551269433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11278261861518745470051821 4229348198069529551269433)
          ·
            refine ⟨3172011148552147163452075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229348198069529551269433 3172011148552147163452075)
            ·
              refine ⟨4758016722828220745178113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172011148552147163452075 4758016722828220745178113)
              ·
                refine ⟨3568512542121165558883585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758016722828220745178113 3568512542121165558883585)
                ·
                  refine ⟨2676384406590874169162689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3568512542121165558883585 2676384406590874169162689)
                  ·
                    refine ⟨2007288304943155626872017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676384406590874169162689 2007288304943155626872017)
                    ·
                      refine ⟨1505466228707366720154013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007288304943155626872017 1505466228707366720154013)
                      ·
                        rfl

theorem cell23_2931885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_2931885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931885 prefixEnd_2931885 := by exact prefixLift 2931885
  have htrace : WordTrace (prefixWord ++ tailWord_2931885) baseStart_2931885 baseEnd_2931885 := by
    simpa [prefixWord, tailWord_2931885, baseEnd_2931885] using wordTrace_append hprefix tailTrace_2931885
  have hstable : (prefixWord ++ tailWord_2931885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931885).length < 2 ^ (prefixWord ++ tailWord_2931885).sum := by decide
  have hdescent : baseEnd_2931885 < baseStart_2931885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931907 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 6, 2]
def baseStart_2931907 : Nat := 118140960795 + 2931907 * 2 ^ 59
def prefixEnd_2931907 : Nat := 4983230072969 + 3 ^ 40 * 2931907 * 2
def baseEnd_2931907 : Nat := 1505477525281765634078911

theorem tailTrace_2931907 : CollatzResearch.WordTrace tailWord_2931907 prefixEnd_2931907 1505477525281765634078911 := by
  unfold tailWord_2931907
  simp only [CollatzResearch.WordTrace]
  refine ⟨106935433389209143695569975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71290288926139429130379983 106935433389209143695569975)
  ·
    refine ⟨160403150083813715543354963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106935433389209143695569975 160403150083813715543354963)
    ·
      refine ⟨240604725125720573315032445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160403150083813715543354963 240604725125720573315032445)
      ·
        refine ⟨90226771922145214993137167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240604725125720573315032445 90226771922145214993137167)
        ·
          refine ⟨135340157883217822489705751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90226771922145214993137167 135340157883217822489705751)
          ·
            refine ⟨203010236824826733734558627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135340157883217822489705751 203010236824826733734558627)
            ·
              refine ⟨304515355237240100601837941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203010236824826733734558627 304515355237240100601837941)
              ·
                refine ⟨28548314553491259431422307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304515355237240100601837941 28548314553491259431422307)
                ·
                  refine ⟨42822471830236889147133461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28548314553491259431422307 42822471830236889147133461)
                  ·
                    refine ⟨2007303367042354178771881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42822471830236889147133461 2007303367042354178771881)
                    ·
                      refine ⟨1505477525281765634078911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007303367042354178771881 1505477525281765634078911)
                      ·
                        rfl

theorem cell23_2931907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_2931907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931907 prefixEnd_2931907 := by exact prefixLift 2931907
  have htrace : WordTrace (prefixWord ++ tailWord_2931907) baseStart_2931907 baseEnd_2931907 := by
    simpa [prefixWord, tailWord_2931907, baseEnd_2931907] using wordTrace_append hprefix tailTrace_2931907
  have hstable : (prefixWord ++ tailWord_2931907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931907).length < 2 ^ (prefixWord ++ tailWord_2931907).sum := by decide
  have hdescent : baseEnd_2931907 < baseStart_2931907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931927 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_2931927 : Nat := 118140960795 + 2931927 * 2 ^ 59
def prefixEnd_2931927 : Nat := 4983230072969 + 3 ^ 40 * 2931927 * 2
def baseEnd_2931927 : Nat := 1505487794894855555828819

theorem tailTrace_2931927 : CollatzResearch.WordTrace tailWord_2931927 prefixEnd_2931927 1505487794894855555828819 := by
  unfold tailWord_2931927
  simp only [CollatzResearch.WordTrace]
  refine ⟨106936162849136687111298035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71290775232757791407532023 106936162849136687111298035)
  ·
    refine ⟨160404244273705030666947053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106936162849136687111298035 160404244273705030666947053)
    ·
      refine ⟨60151591602639386500105145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160404244273705030666947053 60151591602639386500105145)
      ·
        refine ⟨45113693701979539875078859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60151591602639386500105145 45113693701979539875078859)
        ·
          refine ⟨67670540552969309812618289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45113693701979539875078859 67670540552969309812618289)
          ·
            refine ⟨50752905414726982359463717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67670540552969309812618289 50752905414726982359463717)
            ·
              refine ⟨9516169765261309192399447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50752905414726982359463717 9516169765261309192399447)
              ·
                refine ⟨14274254647891963788599171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516169765261309192399447 14274254647891963788599171)
                ·
                  refine ⟨21411381971837945682898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274254647891963788599171 21411381971837945682898757)
                  ·
                    refine ⟨4014634119719614815543517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21411381971837945682898757 4014634119719614815543517)
                    ·
                      refine ⟨1505487794894855555828819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014634119719614815543517 1505487794894855555828819)
                      ·
                        rfl

theorem cell23_2931927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_2931927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931927 prefixEnd_2931927 := by exact prefixLift 2931927
  have htrace : WordTrace (prefixWord ++ tailWord_2931927) baseStart_2931927 baseEnd_2931927 := by
    simpa [prefixWord, tailWord_2931927, baseEnd_2931927] using wordTrace_append hprefix tailTrace_2931927
  have hstable : (prefixWord ++ tailWord_2931927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931927).length < 2 ^ (prefixWord ++ tailWord_2931927).sum := by decide
  have hdescent : baseEnd_2931927 < baseStart_2931927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931944 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2931944 : Nat := 118140960795 + 2931944 * 2 ^ 59
def prefixEnd_2931944 : Nat := 4983230072969 + 3 ^ 40 * 2931944 * 2
def baseEnd_2931944 : Nat := 1505496524065981989316241

theorem tailTrace_2931944 : CollatzResearch.WordTrace tailWord_2931944 prefixEnd_2931944 1505496524065981989316241 := by
  unfold tailWord_2931944
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468391445037549507333443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71291188593383399343111257 53468391445037549507333443)
  ·
    refine ⟨80202587167556324261000165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53468391445037549507333443 80202587167556324261000165)
    ·
      refine ⟨15037985093916810798937531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80202587167556324261000165 15037985093916810798937531)
      ·
        refine ⟨22556977640875216198406297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15037985093916810798937531 22556977640875216198406297)
        ·
          refine ⟨16917733230656412148804723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22556977640875216198406297 16917733230656412148804723)
          ·
            refine ⟨25376599845984618223207085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16917733230656412148804723 25376599845984618223207085)
            ·
              refine ⟨9516224942244231833702657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25376599845984618223207085 9516224942244231833702657)
              ·
                refine ⟨7137168706683173875276993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516224942244231833702657 7137168706683173875276993)
                ·
                  refine ⟨5352876530012380406457745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7137168706683173875276993 5352876530012380406457745)
                  ·
                    refine ⟨4014657397509285304843309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352876530012380406457745 4014657397509285304843309)
                    ·
                      refine ⟨1505496524065981989316241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014657397509285304843309 1505496524065981989316241)
                      ·
                        rfl

theorem cell23_2931944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2931944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931944 prefixEnd_2931944 := by exact prefixLift 2931944
  have htrace : WordTrace (prefixWord ++ tailWord_2931944) baseStart_2931944 baseEnd_2931944 := by
    simpa [prefixWord, tailWord_2931944, baseEnd_2931944] using wordTrace_append hprefix tailTrace_2931944
  have hstable : (prefixWord ++ tailWord_2931944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931944).length < 2 ^ (prefixWord ++ tailWord_2931944).sum := by decide
  have hdescent : baseEnd_2931944 < baseStart_2931944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931951 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 3, 4]
def baseStart_2931951 : Nat := 118140960795 + 2931951 * 2 ^ 59
def prefixEnd_2931951 : Nat := 4983230072969 + 3 ^ 40 * 2931951 * 2
def baseEnd_2931951 : Nat := 501833372810187820642903

theorem tailTrace_2931951 : CollatzResearch.WordTrace tailWord_2931951 prefixEnd_2931951 501833372810187820642903 := by
  unfold tailWord_2931951
  simp only [CollatzResearch.WordTrace]
  refine ⟨106937038201049739210171707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71291358800699826140114471 106937038201049739210171707)
  ·
    refine ⟨160405557301574608815257561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106937038201049739210171707 160405557301574608815257561)
    ·
      refine ⟨120304167976180956611443171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160405557301574608815257561 120304167976180956611443171)
      ·
        refine ⟨180456251964271434917164757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120304167976180956611443171 180456251964271434917164757)
        ·
          refine ⟨4229443405412611755871049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 180456251964271434917164757 4229443405412611755871049)
          ·
            refine ⟨3172082554059458816903287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229443405412611755871049 3172082554059458816903287)
            ·
              refine ⟨4758123831089188225354931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172082554059458816903287 4758123831089188225354931)
              ·
                refine ⟨7137185746633782338032397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758123831089188225354931 7137185746633782338032397)
                ·
                  refine ⟨2676444654987668376762149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7137185746633782338032397 2676444654987668376762149)
                  ·
                    refine ⟨501833372810187820642903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676444654987668376762149 501833372810187820642903)
                    ·
                      rfl

theorem cell23_2931951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_2931951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931951 prefixEnd_2931951 := by exact prefixLift 2931951
  have htrace : WordTrace (prefixWord ++ tailWord_2931951) baseStart_2931951 baseEnd_2931951 := by
    simpa [prefixWord, tailWord_2931951, baseEnd_2931951] using wordTrace_append hprefix tailTrace_2931951
  have hstable : (prefixWord ++ tailWord_2931951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931951).length < 2 ^ (prefixWord ++ tailWord_2931951).sum := by decide
  have hdescent : baseEnd_2931951 < baseStart_2931951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931960 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_2931960 : Nat := 118140960795 + 2931960 * 2 ^ 59
def prefixEnd_2931960 : Nat := 4983230072969 + 3 ^ 40 * 2931960 * 2
def baseEnd_2931960 : Nat := 501834913252151308905389

theorem tailTrace_2931960 : CollatzResearch.WordTrace tailWord_2931960 prefixEnd_2931960 501834913252151308905389 := by
  unfold tailWord_2931960
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468683229008566873624667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71291577638678089164832889 53468683229008566873624667)
  ·
    refine ⟨80203024843512850310437001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53468683229008566873624667 80203024843512850310437001)
    ·
      refine ⟨60152268632634637732827751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80203024843512850310437001 60152268632634637732827751)
      ·
        refine ⟨90228402948951956599241627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60152268632634637732827751 90228402948951956599241627)
        ·
          refine ⟨135342604423427934898862441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90228402948951956599241627 135342604423427934898862441)
          ·
            refine ⟨101506953317570951174146831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135342604423427934898862441 101506953317570951174146831)
            ·
              refine ⟨152260429976356426761220247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101506953317570951174146831 152260429976356426761220247)
              ·
                refine ⟨228390644964534640141830371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152260429976356426761220247 228390644964534640141830371)
                ·
                  refine ⟨342585967446801960212745557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228390644964534640141830371 342585967446801960212745557)
                  ·
                    refine ⟨501834913252151308905389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 342585967446801960212745557 501834913252151308905389)
                    ·
                      rfl

theorem cell23_2931960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_2931960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931960 prefixEnd_2931960 := by exact prefixLift 2931960
  have htrace : WordTrace (prefixWord ++ tailWord_2931960) baseStart_2931960 baseEnd_2931960 := by
    simpa [prefixWord, tailWord_2931960, baseEnd_2931960] using wordTrace_append hprefix tailTrace_2931960
  have hstable : (prefixWord ++ tailWord_2931960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931960).length < 2 ^ (prefixWord ++ tailWord_2931960).sum := by decide
  have hdescent : baseEnd_2931960 < baseStart_2931960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931964 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 6]
def baseStart_2931964 : Nat := 118140960795 + 2931964 * 2 ^ 59
def prefixEnd_2931964 : Nat := 4983230072969 + 3 ^ 40 * 2931964 * 2
def baseEnd_2931964 : Nat := 167278532631007990118461

theorem tailTrace_2931964 : CollatzResearch.WordTrace tailWord_2931964 prefixEnd_2931964 167278532631007990118461 := by
  unfold tailWord_2931964
  simp only [CollatzResearch.WordTrace]
  refine ⟨53468756175001321215197473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71291674900001761620263297 53468756175001321215197473)
  ·
    refine ⟨40101567131250990911398105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53468756175001321215197473 40101567131250990911398105)
    ·
      refine ⟨30076175348438243183548579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40101567131250990911398105 30076175348438243183548579)
      ·
        refine ⟨45114263022657364775322869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30076175348438243183548579 45114263022657364775322869)
        ·
          refine ⟨4229462158374127947686519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45114263022657364775322869 4229462158374127947686519)
          ·
            refine ⟨6344193237561191921529779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229462158374127947686519 6344193237561191921529779)
            ·
              refine ⟨9516289856341787882294669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344193237561191921529779 9516289856341787882294669)
              ·
                refine ⟨3568608696128170455860501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9516289856341787882294669 3568608696128170455860501)
                ·
                  refine ⟨167278532631007990118461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3568608696128170455860501 167278532631007990118461)
                  ·
                    rfl

theorem cell23_2931964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_2931964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931964 prefixEnd_2931964 := by exact prefixLift 2931964
  have htrace : WordTrace (prefixWord ++ tailWord_2931964) baseStart_2931964 baseEnd_2931964 := by
    simpa [prefixWord, tailWord_2931964, baseEnd_2931964] using wordTrace_append hprefix tailTrace_2931964
  have hstable : (prefixWord ++ tailWord_2931964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931964).length < 2 ^ (prefixWord ++ tailWord_2931964).sum := by decide
  have hdescent : baseEnd_2931964 < baseStart_2931964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931977 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_2931977 : Nat := 118140960795 + 2931977 * 2 ^ 59
def prefixEnd_2931977 : Nat := 4983230072969 + 3 ^ 40 * 2931977 * 2
def baseEnd_2931977 : Nat := 501837822975860120067863

theorem tailTrace_2931977 : CollatzResearch.WordTrace tailWord_2931977 prefixEnd_2931977 501837822975860120067863 := by
  unfold tailWord_2931977
  simp only [CollatzResearch.WordTrace]
  refine ⟨106937986498955545650618185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71291990999303697100412123 106937986498955545650618185)
  ·
    refine ⟨80203489874216659237963639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106937986498955545650618185 80203489874216659237963639)
    ·
      refine ⟨120305234811324988856945459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80203489874216659237963639 120305234811324988856945459)
      ·
        refine ⟨180457852216987483285418189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120305234811324988856945459 180457852216987483285418189)
        ·
          refine ⟨67671694581370306232031821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180457852216987483285418189 67671694581370306232031821)
          ·
            refine ⟨25376885468013864837011933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67671694581370306232031821 25376885468013864837011933)
            ·
              refine ⟨9516332050505199313879475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25376885468013864837011933 9516332050505199313879475)
              ·
                refine ⟨14274498075757798970819213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516332050505199313879475 14274498075757798970819213)
                ·
                  refine ⟨5352936778409174614057205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14274498075757798970819213 5352936778409174614057205)
                  ·
                    refine ⟨501837822975860120067863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5352936778409174614057205 501837822975860120067863)
                    ·
                      rfl

theorem cell23_2931977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_2931977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931977 prefixEnd_2931977 := by exact prefixLift 2931977
  have htrace : WordTrace (prefixWord ++ tailWord_2931977) baseStart_2931977 baseEnd_2931977 := by
    simpa [prefixWord, tailWord_2931977, baseEnd_2931977] using wordTrace_append hprefix tailTrace_2931977
  have hstable : (prefixWord ++ tailWord_2931977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931977).length < 2 ^ (prefixWord ++ tailWord_2931977).sum := by decide
  have hdescent : baseEnd_2931977 < baseStart_2931977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2931998 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2931998 : Nat := 118140960795 + 2931998 * 2 ^ 59
def prefixEnd_2931998 : Nat := 4983230072969 + 3 ^ 40 * 2931998 * 2
def baseEnd_2931998 : Nat := 167280472446813864226777

theorem tailTrace_2931998 : CollatzResearch.WordTrace tailWord_2931998 prefixEnd_2931998 167280472446813864226777 := by
  unfold tailWord_2931998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367344053984933279641581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71292501621252977491421765 13367344053984933279641581)
  ·
    refine ⟨5012754020244349979865593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13367344053984933279641581 5012754020244349979865593)
    ·
      refine ⟨3759565515183262484899195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5012754020244349979865593 3759565515183262484899195)
      ·
        refine ⟨5639348272774893727348793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759565515183262484899195 5639348272774893727348793)
        ·
          refine ⟨4229511204581170295511595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5639348272774893727348793 4229511204581170295511595)
          ·
            refine ⟨6344266806871755443267393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229511204581170295511595 6344266806871755443267393)
            ·
              refine ⟨4758200105153816582450545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6344266806871755443267393 4758200105153816582450545)
              ·
                refine ⟨3568650078865362436837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758200105153816582450545 3568650078865362436837909)
                ·
                  refine ⟨167280472446813864226777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3568650078865362436837909 167280472446813864226777)
                  ·
                    rfl

theorem cell23_2931998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2931998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2931998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2931998 prefixEnd_2931998 := by exact prefixLift 2931998
  have htrace : WordTrace (prefixWord ++ tailWord_2931998) baseStart_2931998 baseEnd_2931998 := by
    simpa [prefixWord, tailWord_2931998, baseEnd_2931998] using wordTrace_append hprefix tailTrace_2931998
  have hstable : (prefixWord ++ tailWord_2931998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2931998).length < 2 ^ (prefixWord ++ tailWord_2931998).sum := by decide
  have hdescent : baseEnd_2931998 < baseStart_2931998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2931998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932002 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2932002 : Nat := 118140960795 + 2932002 * 2 ^ 59
def prefixEnd_2932002 : Nat := 4983230072969 + 3 ^ 40 * 2932002 * 2
def baseEnd_2932002 : Nat := 501842101981314254130325

theorem tailTrace_2932002 : CollatzResearch.WordTrace tailWord_2932002 prefixEnd_2932002 501842101981314254130325 := by
  unfold tailWord_2932002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26734724580966243730069565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71292598882576649946852173 26734724580966243730069565)
  ·
    refine ⟨10025521717862341398776087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26734724580966243730069565 10025521717862341398776087)
    ·
      refine ⟨15038282576793512098164131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025521717862341398776087 15038282576793512098164131)
      ·
        refine ⟨22557423865190268147246197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15038282576793512098164131 22557423865190268147246197)
        ·
          refine ⟨2114758487361587638804331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22557423865190268147246197 2114758487361587638804331)
          ·
            refine ⟨3172137731042381458206497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114758487361587638804331 3172137731042381458206497)
            ·
              refine ⟨2379103298281786093654873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172137731042381458206497 2379103298281786093654873)
              ·
                refine ⟨1784327473711339570241155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2379103298281786093654873 1784327473711339570241155)
                ·
                  refine ⟨2676491210567009355361733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784327473711339570241155 2676491210567009355361733)
                  ·
                    refine ⟨501842101981314254130325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676491210567009355361733 501842101981314254130325)
                    ·
                      rfl

theorem cell23_2932002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2932002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932002 prefixEnd_2932002 := by exact prefixLift 2932002
  have htrace : WordTrace (prefixWord ++ tailWord_2932002) baseStart_2932002 baseEnd_2932002 := by
    simpa [prefixWord, tailWord_2932002, baseEnd_2932002] using wordTrace_append hprefix tailTrace_2932002
  have hstable : (prefixWord ++ tailWord_2932002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932002).length < 2 ^ (prefixWord ++ tailWord_2932002).sum := by decide
  have hdescent : baseEnd_2932002 < baseStart_2932002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932031 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 5, 2, 2]
def baseStart_2932031 : Nat := 118140960795 + 2932031 * 2 ^ 59
def prefixEnd_2932031 : Nat := 4983230072969 + 3 ^ 40 * 2932031 * 2
def baseEnd_2932031 : Nat := 1505541196882923148928341

theorem tailTrace_2932031 : CollatzResearch.WordTrace tailWord_2932031 prefixEnd_2932031 1505541196882923148928341 := by
  unfold tailWord_2932031
  simp only [CollatzResearch.WordTrace]
  refine ⟨106939956040759912873083947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71293304027173275248722631 106939956040759912873083947)
  ·
    refine ⟨160409934061139869309625921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106939956040759912873083947 160409934061139869309625921)
    ·
      refine ⟨120307450545854901982219441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160409934061139869309625921 120307450545854901982219441)
      ·
        refine ⟨90230587909391176486664581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120307450545854901982219441 90230587909391176486664581)
        ·
          refine ⟨16918235233010845591249609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90230587909391176486664581 16918235233010845591249609)
          ·
            refine ⟨12688676424758134193437207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16918235233010845591249609 12688676424758134193437207)
            ·
              refine ⟨19033014637137201290155811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12688676424758134193437207 19033014637137201290155811)
              ·
                refine ⟨28549521955705801935233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19033014637137201290155811 28549521955705801935233717)
                ·
                  refine ⟨2676517683347418931428161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28549521955705801935233717 2676517683347418931428161)
                  ·
                    refine ⟨2007388262510564198571121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676517683347418931428161 2007388262510564198571121)
                    ·
                      refine ⟨1505541196882923148928341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007388262510564198571121 1505541196882923148928341)
                      ·
                        rfl

theorem cell23_2932031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_2932031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932031 prefixEnd_2932031 := by exact prefixLift 2932031
  have htrace : WordTrace (prefixWord ++ tailWord_2932031) baseStart_2932031 baseEnd_2932031 := by
    simpa [prefixWord, tailWord_2932031, baseEnd_2932031] using wordTrace_append hprefix tailTrace_2932031
  have hstable : (prefixWord ++ tailWord_2932031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932031).length < 2 ^ (prefixWord ++ tailWord_2932031).sum := by decide
  have hdescent : baseEnd_2932031 < baseStart_2932031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932044 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2932044 : Nat := 118140960795 + 2932044 * 2 ^ 59
def prefixEnd_2932044 : Nat := 4983230072969 + 3 ^ 40 * 2932044 * 2
def baseEnd_2932044 : Nat := 1505547872131431598065781

theorem tailTrace_2932044 : CollatzResearch.WordTrace tailWord_2932044 prefixEnd_2932044 1505547872131431598065781 := by
  unfold tailWord_2932044
  simp only [CollatzResearch.WordTrace]
  refine ⟨53470215094856408046653593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71293620126475210728871457 53470215094856408046653593)
  ·
    refine ⟨40102661321142306034990195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53470215094856408046653593 40102661321142306034990195)
    ·
      refine ⟨60153991981713459052485293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40102661321142306034990195 60153991981713459052485293)
      ·
        refine ⟨22557746993142547144681985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60153991981713459052485293 22557746993142547144681985)
        ·
          refine ⟨16918310244856910358511489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22557746993142547144681985 16918310244856910358511489)
          ·
            refine ⟨12688732683642682768883617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16918310244856910358511489 12688732683642682768883617)
            ·
              refine ⟨9516549512732012076662713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12688732683642682768883617 9516549512732012076662713)
              ·
                refine ⟨7137412134549009057497035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516549512732012076662713 7137412134549009057497035)
                ·
                  refine ⟨10706118201823513586245553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7137412134549009057497035 10706118201823513586245553)
                  ·
                    refine ⟨8029588651367635189684165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10706118201823513586245553 8029588651367635189684165)
                    ·
                      refine ⟨1505547872131431598065781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8029588651367635189684165 1505547872131431598065781)
                      ·
                        rfl

theorem cell23_2932044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2932044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932044 prefixEnd_2932044 := by exact prefixLift 2932044
  have htrace : WordTrace (prefixWord ++ tailWord_2932044) baseStart_2932044 baseEnd_2932044 := by
    simpa [prefixWord, tailWord_2932044, baseEnd_2932044] using wordTrace_append hprefix tailTrace_2932044
  have hstable : (prefixWord ++ tailWord_2932044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932044).length < 2 ^ (prefixWord ++ tailWord_2932044).sum := by decide
  have hdescent : baseEnd_2932044 < baseStart_2932044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932047 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_2932047 : Nat := 118140960795 + 2932047 * 2 ^ 59
def prefixEnd_2932047 : Nat := 4983230072969 + 3 ^ 40 * 2932047 * 2
def baseEnd_2932047 : Nat := 1505549412573395086328267

theorem tailTrace_2932047 : CollatzResearch.WordTrace tailWord_2932047 prefixEnd_2932047 1505549412573395086328267 := by
  unfold tailWord_2932047
  simp only [CollatzResearch.WordTrace]
  refine ⟨106940539608701947605666395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71293693072467965070444263 106940539608701947605666395)
  ·
    refine ⟨160410809413052921408499593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106940539608701947605666395 160410809413052921408499593)
    ·
      refine ⟨120308107059789691056374695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160410809413052921408499593 120308107059789691056374695)
      ·
        refine ⟨180462160589684536584562043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120308107059789691056374695 180462160589684536584562043)
        ·
          refine ⟨270693240884526804876843065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180462160589684536584562043 270693240884526804876843065)
          ·
            refine ⟨203019930663395103657632299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270693240884526804876843065 203019930663395103657632299)
            ·
              refine ⟨304529895995092655486448449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203019930663395103657632299 304529895995092655486448449)
              ·
                refine ⟨228397421996319491614836337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304529895995092655486448449 228397421996319491614836337)
                ·
                  refine ⟨171298066497239618711127253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228397421996319491614836337 171298066497239618711127253)
                  ·
                    refine ⟨4014798433529053563542045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171298066497239618711127253 4014798433529053563542045)
                    ·
                      refine ⟨1505549412573395086328267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014798433529053563542045 1505549412573395086328267)
                      ·
                        rfl

theorem cell23_2932047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_2932047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932047 prefixEnd_2932047 := by exact prefixLift 2932047
  have htrace : WordTrace (prefixWord ++ tailWord_2932047) baseStart_2932047 baseEnd_2932047 := by
    simpa [prefixWord, tailWord_2932047, baseEnd_2932047] using wordTrace_append hprefix tailTrace_2932047
  have hstable : (prefixWord ++ tailWord_2932047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932047).length < 2 ^ (prefixWord ++ tailWord_2932047).sum := by decide
  have hdescent : baseEnd_2932047 < baseStart_2932047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932081 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_2932081 : Nat := 118140960795 + 2932081 * 2 ^ 59
def prefixEnd_2932081 : Nat := 4983230072969 + 3 ^ 40 * 2932081 * 2
def baseEnd_2932081 : Nat := 1505566870915647953303111

theorem tailTrace_2932081 : CollatzResearch.WordTrace tailWord_2932081 prefixEnd_2932081 1505566870915647953303111 := by
  unfold tailWord_2932081
  simp only [CollatzResearch.WordTrace]
  refine ⟨106941779690578771412404097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71294519793719180941602731 106941779690578771412404097)
  ·
    refine ⟨80206334767934078559303073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106941779690578771412404097 80206334767934078559303073)
    ·
      refine ⟨60154751075950558919477305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80206334767934078559303073 60154751075950558919477305)
      ·
        refine ⟨45116063306962919189607979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60154751075950558919477305 45116063306962919189607979)
        ·
          refine ⟨67674094960444378784411969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45116063306962919189607979 67674094960444378784411969)
          ·
            refine ⟨50755571220333284088308977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67674094960444378784411969 50755571220333284088308977)
            ·
              refine ⟨38066678415249963066231733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50755571220333284088308977 38066678415249963066231733)
              ·
                refine ⟨3568751101429684037459225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38066678415249963066231733 3568751101429684037459225)
                ·
                  refine ⟨2676563326072263028094419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3568751101429684037459225 2676563326072263028094419)
                  ·
                    refine ⟨4014844989108394542141629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2676563326072263028094419 4014844989108394542141629)
                    ·
                      refine ⟨1505566870915647953303111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014844989108394542141629 1505566870915647953303111)
                      ·
                        rfl

theorem cell23_2932081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_2932081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932081 prefixEnd_2932081 := by exact prefixLift 2932081
  have htrace : WordTrace (prefixWord ++ tailWord_2932081) baseStart_2932081 baseEnd_2932081 := by
    simpa [prefixWord, tailWord_2932081, baseEnd_2932081] using wordTrace_append hprefix tailTrace_2932081
  have hstable : (prefixWord ++ tailWord_2932081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932081).length < 2 ^ (prefixWord ++ tailWord_2932081).sum := by decide
  have hdescent : baseEnd_2932081 < baseStart_2932081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932141 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2932141 : Nat := 118140960795 + 2932141 * 2 ^ 59
def prefixEnd_2932141 : Nat := 4983230072969 + 3 ^ 40 * 2932141 * 2
def baseEnd_2932141 : Nat := 1505597679754917718552835

theorem tailTrace_2932141 : CollatzResearch.WordTrace tailWord_2932141 prefixEnd_2932141 1505597679754917718552835 := by
  unfold tailWord_2932141
  simp only [CollatzResearch.WordTrace]
  refine ⟨106943968070361401659588277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71295978713574267773058851 106943968070361401659588277)
  ·
    refine ⟨10025997006596381405586401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106943968070361401659588277 10025997006596381405586401)
    ·
      refine ⟨7519497754947286054189801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10025997006596381405586401 7519497754947286054189801)
      ·
        refine ⟨5639623316210464540642351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7519497754947286054189801 5639623316210464540642351)
        ·
          refine ⟨8459434974315696810963527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639623316210464540642351 8459434974315696810963527)
          ·
            refine ⟨12689152461473545216445291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459434974315696810963527 12689152461473545216445291)
            ·
              refine ⟨19033728692210317824667937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12689152461473545216445291 19033728692210317824667937)
              ·
                refine ⟨14275296519157738368500953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19033728692210317824667937 14275296519157738368500953)
                ·
                  refine ⟨10706472389368303776375715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14275296519157738368500953 10706472389368303776375715)
                  ·
                    refine ⟨16059708584052455664563573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10706472389368303776375715 16059708584052455664563573)
                    ·
                      refine ⟨1505597679754917718552835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16059708584052455664563573 1505597679754917718552835)
                      ·
                        rfl

theorem cell23_2932141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2932141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932141 prefixEnd_2932141 := by exact prefixLift 2932141
  have htrace : WordTrace (prefixWord ++ tailWord_2932141) baseStart_2932141 baseEnd_2932141 := by
    simpa [prefixWord, tailWord_2932141, baseEnd_2932141] using wordTrace_append hprefix tailTrace_2932141
  have hstable : (prefixWord ++ tailWord_2932141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932141).length < 2 ^ (prefixWord ++ tailWord_2932141).sum := by decide
  have hdescent : baseEnd_2932141 < baseStart_2932141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932147 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_2932147 : Nat := 118140960795 + 2932147 * 2 ^ 59
def prefixEnd_2932147 : Nat := 4983230072969 + 3 ^ 40 * 2932147 * 2
def baseEnd_2932147 : Nat := 1505600760638844695077807

theorem tailTrace_2932147 : CollatzResearch.WordTrace tailWord_2932147 prefixEnd_2932147 1505600760638844695077807 := by
  unfold tailWord_2932147
  simp only [CollatzResearch.WordTrace]
  refine ⟨106944186908339664684306695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71296124605559776456204463 106944186908339664684306695)
  ·
    refine ⟨160416280362509497026460043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106944186908339664684306695 160416280362509497026460043)
    ·
      refine ⟨240624420543764245539690065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160416280362509497026460043 240624420543764245539690065)
      ·
        refine ⟨180468315407823184154767549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240624420543764245539690065 180468315407823184154767549)
        ·
          refine ⟨67675618277933694058037831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180468315407823184154767549 67675618277933694058037831)
          ·
            refine ⟨101513427416900541087056747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67675618277933694058037831 101513427416900541087056747)
            ·
              refine ⟨152270141125350811630585121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101513427416900541087056747 152270141125350811630585121)
              ·
                refine ⟨114202605844013108722938841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152270141125350811630585121 114202605844013108722938841)
                ·
                  refine ⟨85651954383009831542204131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114202605844013108722938841 85651954383009831542204131)
                  ·
                    refine ⟨128477931574514747313306197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85651954383009831542204131 128477931574514747313306197)
                    ·
                      refine ⟨1505600760638844695077807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128477931574514747313306197 1505600760638844695077807)
                      ·
                        rfl

theorem cell23_2932147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_2932147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932147 prefixEnd_2932147 := by exact prefixLift 2932147
  have htrace : WordTrace (prefixWord ++ tailWord_2932147) baseStart_2932147 baseEnd_2932147 := by
    simpa [prefixWord, tailWord_2932147, baseEnd_2932147] using wordTrace_append hprefix tailTrace_2932147
  have hstable : (prefixWord ++ tailWord_2932147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932147).length < 2 ^ (prefixWord ++ tailWord_2932147).sum := by decide
  have hdescent : baseEnd_2932147 < baseStart_2932147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932154 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3]
def baseStart_2932154 : Nat := 118140960795 + 2932154 * 2 ^ 59
def prefixEnd_2932154 : Nat := 4983230072969 + 3 ^ 40 * 2932154 * 2
def baseEnd_2932154 : Nat := 1505604355003426167690275

theorem tailTrace_2932154 : CollatzResearch.WordTrace tailWord_2932154 prefixEnd_2932154 1505604355003426167690275 := by
  unfold tailWord_2932154
  simp only [CollatzResearch.WordTrace]
  refine ⟨26736110554828576219952879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71296294812876203253207677 26736110554828576219952879)
  ·
    refine ⟨40104165832242864329929319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26736110554828576219952879 40104165832242864329929319)
    ·
      refine ⟨60156248748364296494893979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40104165832242864329929319 60156248748364296494893979)
      ·
        refine ⟨90234373122546444742340969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60156248748364296494893979 90234373122546444742340969)
        ·
          refine ⟨67675779841909833556755727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90234373122546444742340969 67675779841909833556755727)
          ·
            refine ⟨101513669762864750335133591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67675779841909833556755727 101513669762864750335133591)
            ·
              refine ⟨152270504644297125502700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101513669762864750335133591 152270504644297125502700387)
              ·
                refine ⟨228405756966445688254050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152270504644297125502700387 228405756966445688254050581)
                ·
                  refine ⟨10706519857802141636908621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 228405756966445688254050581 10706519857802141636908621)
                  ·
                    refine ⟨4014944946675803113840733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10706519857802141636908621 4014944946675803113840733)
                    ·
                      refine ⟨1505604355003426167690275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4014944946675803113840733 1505604355003426167690275)
                      ·
                        rfl

theorem cell23_2932154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_2932154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932154 prefixEnd_2932154 := by exact prefixLift 2932154
  have htrace : WordTrace (prefixWord ++ tailWord_2932154) baseStart_2932154 baseEnd_2932154 := by
    simpa [prefixWord, tailWord_2932154, baseEnd_2932154] using wordTrace_append hprefix tailTrace_2932154
  have hstable : (prefixWord ++ tailWord_2932154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932154).length < 2 ^ (prefixWord ++ tailWord_2932154).sum := by decide
  have hdescent : baseEnd_2932154 < baseStart_2932154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932181 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2932181 : Nat := 118140960795 + 2932181 * 2 ^ 59
def prefixEnd_2932181 : Nat := 4983230072969 + 3 ^ 40 * 2932181 * 2
def baseEnd_2932181 : Nat := 1505618218981097562052651

theorem tailTrace_2932181 : CollatzResearch.WordTrace tailWord_2932181 prefixEnd_2932181 1505618218981097562052651 := by
  unfold tailWord_2932181
  simp only [CollatzResearch.WordTrace]
  refine ⟨106945426990216488491044397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71296951326810992327362931 106945426990216488491044397)
  ·
    refine ⟨40104535121331183184141649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106945426990216488491044397 40104535121331183184141649)
    ·
      refine ⟨30078401340998387388106237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40104535121331183184141649 30078401340998387388106237)
      ·
        refine ⟨11279400502874395270539839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30078401340998387388106237 11279400502874395270539839)
        ·
          refine ⟨16919100754311592905809759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279400502874395270539839 16919100754311592905809759)
          ·
            refine ⟨25378651131467389358714639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16919100754311592905809759 25378651131467389358714639)
            ·
              refine ⟨38067976697201084038071959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25378651131467389358714639 38067976697201084038071959)
              ·
                refine ⟨57101965045801626057107939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38067976697201084038071959 57101965045801626057107939)
                ·
                  refine ⟨85652947568702439085661909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57101965045801626057107939 85652947568702439085661909)
                  ·
                    refine ⟨2007490958641463416070201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85652947568702439085661909 2007490958641463416070201)
                    ·
                      refine ⟨1505618218981097562052651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007490958641463416070201 1505618218981097562052651)
                      ·
                        rfl

theorem cell23_2932181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2932181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932181 prefixEnd_2932181 := by exact prefixLift 2932181
  have htrace : WordTrace (prefixWord ++ tailWord_2932181) baseStart_2932181 baseEnd_2932181 := by
    simpa [prefixWord, tailWord_2932181, baseEnd_2932181] using wordTrace_append hprefix tailTrace_2932181
  have hstable : (prefixWord ++ tailWord_2932181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932181).length < 2 ^ (prefixWord ++ tailWord_2932181).sum := by decide
  have hdescent : baseEnd_2932181 < baseStart_2932181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932184 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2932184 : Nat := 118140960795 + 2932184 * 2 ^ 59
def prefixEnd_2932184 : Nat := 4983230072969 + 3 ^ 40 * 2932184 * 2
def baseEnd_2932184 : Nat := 1505619759423061050315137

theorem tailTrace_2932184 : CollatzResearch.WordTrace tailWord_2932184 prefixEnd_2932184 1505619759423061050315137 := by
  unfold tailWord_2932184
  simp only [CollatzResearch.WordTrace]
  refine ⟨53472768204602810001701803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71297024272803746668935737 53472768204602810001701803)
  ·
    refine ⟨80209152306904215002552705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53472768204602810001701803 80209152306904215002552705)
    ·
      refine ⟨60156864230178161251914529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80209152306904215002552705 60156864230178161251914529)
      ·
        refine ⟨45117648172633620938935897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60156864230178161251914529 45117648172633620938935897)
        ·
          refine ⟨33838236129475215704201923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45117648172633620938935897 33838236129475215704201923)
          ·
            refine ⟨50757354194212823556302885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33838236129475215704201923 50757354194212823556302885)
            ·
              refine ⟨9517003911414904416806791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50757354194212823556302885 9517003911414904416806791)
              ·
                refine ⟨14275505867122356625210187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9517003911414904416806791 14275505867122356625210187)
                ·
                  refine ⟨21413258800683534937815281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14275505867122356625210187 21413258800683534937815281)
                  ·
                    refine ⟨16059944100512651203361461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21413258800683534937815281 16059944100512651203361461)
                    ·
                      refine ⟨1505619759423061050315137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16059944100512651203361461 1505619759423061050315137)
                      ·
                        rfl

theorem cell23_2932184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2932184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932184 prefixEnd_2932184 := by exact prefixLift 2932184
  have htrace : WordTrace (prefixWord ++ tailWord_2932184) baseStart_2932184 baseEnd_2932184 := by
    simpa [prefixWord, tailWord_2932184, baseEnd_2932184] using wordTrace_append hprefix tailTrace_2932184
  have hstable : (prefixWord ++ tailWord_2932184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932184).length < 2 ^ (prefixWord ++ tailWord_2932184).sum := by decide
  have hdescent : baseEnd_2932184 < baseStart_2932184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932328 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2932328 : Nat := 118140960795 + 2932328 * 2 ^ 59
def prefixEnd_2932328 : Nat := 4983230072969 + 3 ^ 40 * 2932328 * 2
def baseEnd_2932328 : Nat := 501897900212436162304825

theorem tailTrace_2932328 : CollatzResearch.WordTrace tailWord_2932328 prefixEnd_2932328 501897900212436162304825 := by
  unfold tailWord_2932328
  simp only [CollatzResearch.WordTrace]
  refine ⟨53475394260341966298322819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71300525680455955064430425 53475394260341966298322819)
  ·
    refine ⟨80213091390512949447484229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53475394260341966298322819 80213091390512949447484229)
    ·
      refine ⟨15039954635721178021403293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80213091390512949447484229 15039954635721178021403293)
      ·
        refine ⟨5639982988395441758026235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15039954635721178021403293 5639982988395441758026235)
        ·
          refine ⟨8459974482593162637039353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639982988395441758026235 8459974482593162637039353)
          ·
            refine ⟨6344980861944871977779515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8459974482593162637039353 6344980861944871977779515)
            ·
              refine ⟨9517471292917307966669273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344980861944871977779515 9517471292917307966669273)
              ·
                refine ⟨7138103469687980975001955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9517471292917307966669273 7138103469687980975001955)
                ·
                  refine ⟨10707155204531971462502933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138103469687980975001955 10707155204531971462502933)
                  ·
                    refine ⟨501897900212436162304825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10707155204531971462502933 501897900212436162304825)
                    ·
                      rfl

theorem cell23_2932328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2932328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932328 prefixEnd_2932328 := by exact prefixLift 2932328
  have htrace : WordTrace (prefixWord ++ tailWord_2932328) baseStart_2932328 baseEnd_2932328 := by
    simpa [prefixWord, tailWord_2932328, baseEnd_2932328] using wordTrace_append hprefix tailTrace_2932328
  have hstable : (prefixWord ++ tailWord_2932328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932328).length < 2 ^ (prefixWord ++ tailWord_2932328).sum := by decide
  have hdescent : baseEnd_2932328 < baseStart_2932328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932338 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2932338 : Nat := 118140960795 + 2932338 * 2 ^ 59
def prefixEnd_2932338 : Nat := 4983230072969 + 3 ^ 40 * 2932338 * 2
def baseEnd_2932338 : Nat := 1505698835443853447789429

theorem tailTrace_2932338 : CollatzResearch.WordTrace tailWord_2932338 prefixEnd_2932338 1505698835443853447789429 := by
  unfold tailWord_2932338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26737788312661926076127417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71300768833765136203006445 26737788312661926076127417)
  ·
    refine ⟨20053341234496444557095563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26737788312661926076127417 20053341234496444557095563)
    ·
      refine ⟨30080011851744666835643345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20053341234496444557095563 30080011851744666835643345)
      ·
        refine ⟨22560008888808500126732509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30080011851744666835643345 22560008888808500126732509)
        ·
          refine ⟨8460003333303187547524691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22560008888808500126732509 8460003333303187547524691)
          ·
            refine ⟨12690004999954781321287037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8460003333303187547524691 12690004999954781321287037)
            ·
              refine ⟨4758751874983042995482639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12690004999954781321287037 4758751874983042995482639)
              ·
                refine ⟨7138127812474564493223959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758751874983042995482639 7138127812474564493223959)
                ·
                  refine ⟨10707191718711846739835939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138127812474564493223959 10707191718711846739835939)
                  ·
                    refine ⟨16060787578067770109753909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10707191718711846739835939 16060787578067770109753909)
                    ·
                      refine ⟨1505698835443853447789429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16060787578067770109753909 1505698835443853447789429)
                      ·
                        rfl

theorem cell23_2932338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2932338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932338 prefixEnd_2932338 := by exact prefixLift 2932338
  have htrace : WordTrace (prefixWord ++ tailWord_2932338) baseStart_2932338 baseEnd_2932338 := by
    simpa [prefixWord, tailWord_2932338, baseEnd_2932338] using wordTrace_append hprefix tailTrace_2932338
  have hstable : (prefixWord ++ tailWord_2932338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932338).length < 2 ^ (prefixWord ++ tailWord_2932338).sum := by decide
  have hdescent : baseEnd_2932338 < baseStart_2932338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932341 : List Nat := [1, 3, 4, 2, 1, 12]
def baseStart_2932341 : Nat := 118140960795 + 2932341 * 2 ^ 59
def prefixEnd_2932341 : Nat := 4983230072969 + 3 ^ 40 * 2932341 * 2
def baseEnd_2932341 : Nat := 6196297843151510024905

theorem tailTrace_2932341 : CollatzResearch.WordTrace tailWord_2932341 prefixEnd_2932341 6196297843151510024905 := by
  unfold tailWord_2932341
  simp only [CollatzResearch.WordTrace]
  refine ⟨106951262669636835816868877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71300841779757890544579251 106951262669636835816868877)
  ·
    refine ⟨40106723501113813431325829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106951262669636835816868877 40106723501113813431325829)
    ·
      refine ⟨7520010656458840018373593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40106723501113813431325829 7520010656458840018373593)
      ·
        refine ⟨5640007992344130013780195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7520010656458840018373593 5640007992344130013780195)
        ·
          refine ⟨8460011988516195020670293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640007992344130013780195 8460011988516195020670293)
          ·
            refine ⟨6196297843151510024905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8460011988516195020670293 6196297843151510024905)
            ·
              rfl

theorem cell23_2932341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 12].length) (baseStart_2932341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932341 prefixEnd_2932341 := by exact prefixLift 2932341
  have htrace : WordTrace (prefixWord ++ tailWord_2932341) baseStart_2932341 baseEnd_2932341 := by
    simpa [prefixWord, tailWord_2932341, baseEnd_2932341] using wordTrace_append hprefix tailTrace_2932341
  have hstable : (prefixWord ++ tailWord_2932341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932341).length < 2 ^ (prefixWord ++ tailWord_2932341).sum := by decide
  have hdescent : baseEnd_2932341 < baseStart_2932341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932352 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 1, 2, 2]
def baseStart_2932352 : Nat := 118140960795 + 2932352 * 2 ^ 59
def prefixEnd_2932352 : Nat := 4983230072969 + 3 ^ 40 * 2932352 * 2
def baseEnd_2932352 : Nat := 1505706024173016393014365

theorem tailTrace_2932352 : CollatzResearch.WordTrace tailWord_2932352 prefixEnd_2932352 1505706024173016393014365 := by
  unfold tailWord_2932352
  simp only [CollatzResearch.WordTrace]
  refine ⟨53475831936298492347759655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71301109248397989797012873 53475831936298492347759655)
  ·
    refine ⟨80213747904447738521639483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53475831936298492347759655 80213747904447738521639483)
    ·
      refine ⟨120320621856671607782459225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80213747904447738521639483 120320621856671607782459225)
      ·
        refine ⟨90240466392503705836844419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120320621856671607782459225 90240466392503705836844419)
        ·
          refine ⟨135360699588755558755266629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90240466392503705836844419 135360699588755558755266629)
          ·
            refine ⟨25380131172891667266612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135360699588755558755266629 25380131172891667266612493)
            ·
              refine ⟨9517549189834375224979685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25380131172891667266612493 9517549189834375224979685)
              ·
                refine ⟨1784540473093945354683691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9517549189834375224979685 1784540473093945354683691)
                ·
                  refine ⟨2676810709640918032025537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784540473093945354683691 2676810709640918032025537)
                  ·
                    refine ⟨2007608032230688524019153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2676810709640918032025537 2007608032230688524019153)
                    ·
                      refine ⟨1505706024173016393014365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007608032230688524019153 1505706024173016393014365)
                      ·
                        rfl

theorem cell23_2932352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_2932352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932352 prefixEnd_2932352 := by exact prefixLift 2932352
  have htrace : WordTrace (prefixWord ++ tailWord_2932352) baseStart_2932352 baseEnd_2932352 := by
    simpa [prefixWord, tailWord_2932352, baseEnd_2932352] using wordTrace_append hprefix tailTrace_2932352
  have hstable : (prefixWord ++ tailWord_2932352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932352).length < 2 ^ (prefixWord ++ tailWord_2932352).sum := by decide
  have hdescent : baseEnd_2932352 < baseStart_2932352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932381 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2932381 : Nat := 118140960795 + 2932381 * 2 ^ 59
def prefixEnd_2932381 : Nat := 4983230072969 + 3 ^ 40 * 2932381 * 2
def baseEnd_2932381 : Nat := 1505720915111996779551731

theorem tailTrace_2932381 : CollatzResearch.WordTrace tailWord_2932381 prefixEnd_2932381 1505720915111996779551731 := by
  unfold tailWord_2932381
  simp only [CollatzResearch.WordTrace]
  refine ⟨106952721589491922648324997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71301814392994615098883331 106952721589491922648324997)
  ·
    refine ⟨20053635298029735496560937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106952721589491922648324997 20053635298029735496560937)
    ·
      refine ⟨15040226473522301622420703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20053635298029735496560937 15040226473522301622420703)
      ·
        refine ⟨22560339710283452433631055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040226473522301622420703 22560339710283452433631055)
        ·
          refine ⟨33840509565425178650446583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560339710283452433631055 33840509565425178650446583)
          ·
            refine ⟨50760764348137767975669875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33840509565425178650446583 50760764348137767975669875)
            ·
              refine ⟨76141146522206651963504813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50760764348137767975669875 76141146522206651963504813)
              ·
                refine ⟨28552929945827494486314305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76141146522206651963504813 28552929945827494486314305)
                ·
                  refine ⟨21414697459370620864735729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28552929945827494486314305 21414697459370620864735729)
                  ·
                    refine ⟨16061023094527965648551797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21414697459370620864735729 16061023094527965648551797)
                    ·
                      refine ⟨1505720915111996779551731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16061023094527965648551797 1505720915111996779551731)
                      ·
                        rfl

theorem cell23_2932381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2932381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932381 prefixEnd_2932381 := by exact prefixLift 2932381
  have htrace : WordTrace (prefixWord ++ tailWord_2932381) baseStart_2932381 baseEnd_2932381 := by
    simpa [prefixWord, tailWord_2932381, baseEnd_2932381] using wordTrace_append hprefix tailTrace_2932381
  have hstable : (prefixWord ++ tailWord_2932381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932381).length < 2 ^ (prefixWord ++ tailWord_2932381).sum := by decide
  have hdescent : baseEnd_2932381 < baseStart_2932381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932386 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2932386 : Nat := 118140960795 + 2932386 * 2 ^ 59
def prefixEnd_2932386 : Nat := 4983230072969 + 3 ^ 40 * 2932386 * 2
def baseEnd_2932386 : Nat := 1505723482515269259989209

theorem tailTrace_2932386 : CollatzResearch.WordTrace tailWord_2932386 prefixEnd_2932386 1505723482515269259989209 := by
  unfold tailWord_2932386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738225988618452125564253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71301935969649205668171341 26738225988618452125564253)
  ·
    refine ⟨10026834745731919547086595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26738225988618452125564253 10026834745731919547086595)
    ·
      refine ⟨15040252118597879320629893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10026834745731919547086595 15040252118597879320629893)
      ·
        refine ⟨2820047272237102372618105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15040252118597879320629893 2820047272237102372618105)
        ·
          refine ⟨2115035454177826779463579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820047272237102372618105 2115035454177826779463579)
          ·
            refine ⟨3172553181266740169195369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115035454177826779463579 3172553181266740169195369)
            ·
              refine ⟨2379414885950055126896527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3172553181266740169195369 2379414885950055126896527)
              ·
                refine ⟨3569122328925082690344791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2379414885950055126896527 3569122328925082690344791)
                ·
                  refine ⟨5353683493387624035517187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569122328925082690344791 5353683493387624035517187)
                  ·
                    refine ⟨8030525240081436053275781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353683493387624035517187 8030525240081436053275781)
                    ·
                      refine ⟨1505723482515269259989209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8030525240081436053275781 1505723482515269259989209)
                      ·
                        rfl

theorem cell23_2932386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2932386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932386 prefixEnd_2932386 := by exact prefixLift 2932386
  have htrace : WordTrace (prefixWord ++ tailWord_2932386) baseStart_2932386 baseEnd_2932386 := by
    simpa [prefixWord, tailWord_2932386, baseEnd_2932386] using wordTrace_append hprefix tailTrace_2932386
  have hstable : (prefixWord ++ tailWord_2932386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932386).length < 2 ^ (prefixWord ++ tailWord_2932386).sum := by decide
  have hdescent : baseEnd_2932386 < baseStart_2932386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_2932408 : Nat := 118140960795 + 2932408 * 2 ^ 59
def prefixEnd_2932408 : Nat := 4983230072969 + 3 ^ 40 * 2932408 * 2
def baseEnd_2932408 : Nat := 1505734779089668173914107

theorem tailTrace_2932408 : CollatzResearch.WordTrace tailWord_2932408 prefixEnd_2932408 1505734779089668173914107 := by
  unfold tailWord_2932408
  simp only [CollatzResearch.WordTrace]
  refine ⟨53476853180197053129778939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71302470906929404173038585 53476853180197053129778939)
  ·
    refine ⟨80215279770295579694668409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53476853180197053129778939 80215279770295579694668409)
    ·
      refine ⟨60161459827721684771001307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80215279770295579694668409 60161459827721684771001307)
      ·
        refine ⟨90242189741582527156501961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60161459827721684771001307 90242189741582527156501961)
        ·
          refine ⟨67681642306186895367376471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90242189741582527156501961 67681642306186895367376471)
          ·
            refine ⟨101522463459280343051064707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67681642306186895367376471 101522463459280343051064707)
            ·
              refine ⟨152283695188920514576597061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101522463459280343051064707 152283695188920514576597061)
              ·
                refine ⟨28553192847922596483111949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152283695188920514576597061 28553192847922596483111949)
                ·
                  refine ⟨10707447317970973681166981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28553192847922596483111949 10707447317970973681166981)
                  ·
                    refine ⟨2007646372119557565218809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10707447317970973681166981 2007646372119557565218809)
                    ·
                      refine ⟨1505734779089668173914107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007646372119557565218809 1505734779089668173914107)
                      ·
                        rfl

theorem cell23_2932408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_2932408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932408 prefixEnd_2932408 := by exact prefixLift 2932408
  have htrace : WordTrace (prefixWord ++ tailWord_2932408) baseStart_2932408 baseEnd_2932408 := by
    simpa [prefixWord, tailWord_2932408, baseEnd_2932408] using wordTrace_append hprefix tailTrace_2932408
  have hstable : (prefixWord ++ tailWord_2932408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932408).length < 2 ^ (prefixWord ++ tailWord_2932408).sum := by decide
  have hdescent : baseEnd_2932408 < baseStart_2932408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932411 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3]
def baseStart_2932411 : Nat := 118140960795 + 2932411 * 2 ^ 59
def prefixEnd_2932411 : Nat := 4983230072969 + 3 ^ 40 * 2932411 * 2
def baseEnd_2932411 : Nat := 1505736319531631662176593

theorem tailTrace_2932411 : CollatzResearch.WordTrace tailWord_2932411 prefixEnd_2932411 1505736319531631662176593 := by
  unfold tailWord_2932411
  simp only [CollatzResearch.WordTrace]
  refine ⟨106953815779383237771917087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71302543852922158514611391 106953815779383237771917087)
  ·
    refine ⟨160430723669074856657875631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106953815779383237771917087 160430723669074856657875631)
    ·
      refine ⟨240646085503612284986813447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160430723669074856657875631 240646085503612284986813447)
      ·
        refine ⟨360969128255418427480220171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240646085503612284986813447 360969128255418427480220171)
        ·
          refine ⟨541453692383127641220330257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360969128255418427480220171 541453692383127641220330257)
          ·
            refine ⟨406090269287345730915247693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541453692383127641220330257 406090269287345730915247693)
            ·
              refine ⟨152283850982754649093217885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406090269287345730915247693 152283850982754649093217885)
              ·
                refine ⟨57106444118532993409956707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152283850982754649093217885 57106444118532993409956707)
                ·
                  refine ⟨85659666177799490114935061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57106444118532993409956707 85659666177799490114935061)
                  ·
                    refine ⟨4015296852084351099137581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85659666177799490114935061 4015296852084351099137581)
                    ·
                      refine ⟨1505736319531631662176593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015296852084351099137581 1505736319531631662176593)
                      ·
                        rfl

theorem cell23_2932411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].length) (baseStart_2932411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932411 prefixEnd_2932411 := by exact prefixLift 2932411
  have htrace : WordTrace (prefixWord ++ tailWord_2932411) baseStart_2932411 baseEnd_2932411 := by
    simpa [prefixWord, tailWord_2932411, baseEnd_2932411] using wordTrace_append hprefix tailTrace_2932411
  have hstable : (prefixWord ++ tailWord_2932411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932411).length < 2 ^ (prefixWord ++ tailWord_2932411).sum := by decide
  have hdescent : baseEnd_2932411 < baseStart_2932411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932429 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2932429 : Nat := 118140960795 + 2932429 * 2 ^ 59
def prefixEnd_2932429 : Nat := 4983230072969 + 3 ^ 40 * 2932429 * 2
def baseEnd_2932429 : Nat := 1505745562183412591751511

theorem tailTrace_2932429 : CollatzResearch.WordTrace tailWord_2932429 prefixEnd_2932429 1505745562183412591751511 := by
  unfold tailWord_2932429
  simp only [CollatzResearch.WordTrace]
  refine ⟨106954472293318026846072341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71302981528878684564048227 106954472293318026846072341)
  ·
    refine ⟨5013490888749282508409641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106954472293318026846072341 5013490888749282508409641)
    ·
      refine ⟨3760118166561961881307231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5013490888749282508409641 3760118166561961881307231)
      ·
        refine ⟨5640177249842942821960847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760118166561961881307231 5640177249842942821960847)
        ·
          refine ⟨8460265874764414232941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640177249842942821960847 8460265874764414232941271)
          ·
            refine ⟨12690398812146621349411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8460265874764414232941271 12690398812146621349411907)
            ·
              refine ⟨19035598218219932024117861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12690398812146621349411907 19035598218219932024117861)
              ·
                refine ⟨3569174665916237254522099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19035598218219932024117861 3569174665916237254522099)
                ·
                  refine ⟨5353761998874355881783149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569174665916237254522099 5353761998874355881783149)
                  ·
                    refine ⟨2007660749577883455668681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5353761998874355881783149 2007660749577883455668681)
                    ·
                      refine ⟨1505745562183412591751511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007660749577883455668681 1505745562183412591751511)
                      ·
                        rfl

theorem cell23_2932429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2932429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932429 prefixEnd_2932429 := by exact prefixLift 2932429
  have htrace : WordTrace (prefixWord ++ tailWord_2932429) baseStart_2932429 baseEnd_2932429 := by
    simpa [prefixWord, tailWord_2932429, baseEnd_2932429] using wordTrace_append hprefix tailTrace_2932429
  have hstable : (prefixWord ++ tailWord_2932429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932429).length < 2 ^ (prefixWord ++ tailWord_2932429).sum := by decide
  have hdescent : baseEnd_2932429 < baseStart_2932429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932458 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2932458 : Nat := 118140960795 + 2932458 * 2 ^ 59
def prefixEnd_2932458 : Nat := 4983230072969 + 3 ^ 40 * 2932458 * 2
def baseEnd_2932458 : Nat := 1505760453122392978288877

theorem tailTrace_2932458 : CollatzResearch.WordTrace tailWord_2932458 prefixEnd_2932458 1505760453122392978288877 := by
  unfold tailWord_2932458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26738882502553241199719507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71303686673475309865918685 26738882502553241199719507)
  ·
    refine ⟨40108323753829861799579261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26738882502553241199719507 40108323753829861799579261)
    ·
      refine ⟨15040621407686198174842223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40108323753829861799579261 15040621407686198174842223)
      ·
        refine ⟨22560932111529297262263335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040621407686198174842223 22560932111529297262263335)
        ·
          refine ⟨33841398167293945893395003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560932111529297262263335 33841398167293945893395003)
          ·
            refine ⟨50762097250940918840092505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33841398167293945893395003 50762097250940918840092505)
            ·
              refine ⟨38071572938205689130069379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50762097250940918840092505 38071572938205689130069379)
              ·
                refine ⟨57107359407308533695104069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38071572938205689130069379 57107359407308533695104069)
                ·
                  refine ⟨10707629888870350067832013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57107359407308533695104069 10707629888870350067832013)
                  ·
                    refine ⟨4015361208326381275437005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10707629888870350067832013 4015361208326381275437005)
                    ·
                      refine ⟨1505760453122392978288877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015361208326381275437005 1505760453122392978288877)
                      ·
                        rfl

theorem cell23_2932458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2932458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932458 prefixEnd_2932458 := by exact prefixLift 2932458
  have htrace : WordTrace (prefixWord ++ tailWord_2932458) baseStart_2932458 baseEnd_2932458 := by
    simpa [prefixWord, tailWord_2932458, baseEnd_2932458] using wordTrace_append hprefix tailTrace_2932458
  have hstable : (prefixWord ++ tailWord_2932458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932458).length < 2 ^ (prefixWord ++ tailWord_2932458).sum := by decide
  have hdescent : baseEnd_2932458 < baseStart_2932458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932471 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_2932471 : Nat := 118140960795 + 2932471 * 2 ^ 59
def prefixEnd_2932471 : Nat := 4983230072969 + 3 ^ 40 * 2932471 * 2
def baseEnd_2932471 : Nat := 1505767128370901427426317

theorem tailTrace_2932471 : CollatzResearch.WordTrace tailWord_2932471 prefixEnd_2932471 1505767128370901427426317 := by
  unfold tailWord_2932471
  simp only [CollatzResearch.WordTrace]
  refine ⟨106956004159165868019101267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71304002772777245346067511 106956004159165868019101267)
  ·
    refine ⟨160434006238748802028651901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106956004159165868019101267 160434006238748802028651901)
    ·
      refine ⟨60162752339530800760744463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160434006238748802028651901 60162752339530800760744463)
      ·
        refine ⟨90244128509296201141116695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60162752339530800760744463 90244128509296201141116695)
        ·
          refine ⟨135366192763944301711675043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90244128509296201141116695 135366192763944301711675043)
          ·
            refine ⟨203049289145916452567512565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135366192763944301711675043 203049289145916452567512565)
            ·
              refine ⟨19035870857429667428204303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203049289145916452567512565 19035870857429667428204303)
              ·
                refine ⟨28553806286144501142306455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19035870857429667428204303 28553806286144501142306455)
                ·
                  refine ⟨42830709429216751713459683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28553806286144501142306455 42830709429216751713459683)
                  ·
                    refine ⟨64246064143825127570189525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42830709429216751713459683 64246064143825127570189525)
                    ·
                      refine ⟨1505767128370901427426317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64246064143825127570189525 1505767128370901427426317)
                      ·
                        rfl

theorem cell23_2932471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_2932471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932471 prefixEnd_2932471 := by exact prefixLift 2932471
  have htrace : WordTrace (prefixWord ++ tailWord_2932471) baseStart_2932471 baseEnd_2932471 := by
    simpa [prefixWord, tailWord_2932471, baseEnd_2932471] using wordTrace_append hprefix tailTrace_2932471
  have hstable : (prefixWord ++ tailWord_2932471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932471).length < 2 ^ (prefixWord ++ tailWord_2932471).sum := by decide
  have hdescent : baseEnd_2932471 < baseStart_2932471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932491 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 8]
def baseStart_2932491 : Nat := 118140960795 + 2932491 * 2 ^ 59
def prefixEnd_2932491 : Nat := 4983230072969 + 3 ^ 40 * 2932491 * 2
def baseEnd_2932491 : Nat := 501925799327997116392075

theorem tailTrace_2932491 : CollatzResearch.WordTrace tailWord_2932491 prefixEnd_2932491 501925799327997116392075 := by
  unfold tailWord_2932491
  simp only [CollatzResearch.WordTrace]
  refine ⟨106956733619093411434829327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71304489079395607623219551 106956733619093411434829327)
  ·
    refine ⟨160435100428640117152243991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106956733619093411434829327 160435100428640117152243991)
    ·
      refine ⟨240652650642960175728365987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160435100428640117152243991 240652650642960175728365987)
      ·
        refine ⟨360978975964440263592548981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240652650642960175728365987 360978975964440263592548981)
        ·
          refine ⟨33841778996666274711801467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 360978975964440263592548981 33841778996666274711801467)
          ·
            refine ⟨50762668494999412067702201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33841778996666274711801467 50762668494999412067702201)
            ·
              refine ⟨38072001371249559050776651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50762668494999412067702201 38072001371249559050776651)
              ·
                refine ⟨57108002056874338576164977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38072001371249559050776651 57108002056874338576164977)
                ·
                  refine ⟨42831001542655753932123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57108002056874338576164977 42831001542655753932123733)
                  ·
                    refine ⟨501925799327997116392075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42831001542655753932123733 501925799327997116392075)
                    ·
                      rfl

theorem cell23_2932491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_2932491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932491 prefixEnd_2932491 := by exact prefixLift 2932491
  have htrace : WordTrace (prefixWord ++ tailWord_2932491) baseStart_2932491 baseEnd_2932491 := by
    simpa [prefixWord, tailWord_2932491, baseEnd_2932491] using wordTrace_append hprefix tailTrace_2932491
  have hstable : (prefixWord ++ tailWord_2932491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932491).length < 2 ^ (prefixWord ++ tailWord_2932491).sum := by decide
  have hdescent : baseEnd_2932491 < baseStart_2932491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932493 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2932493 : Nat := 118140960795 + 2932493 * 2 ^ 59
def prefixEnd_2932493 : Nat := 4983230072969 + 3 ^ 40 * 2932493 * 2
def baseEnd_2932493 : Nat := 1505778424945300341351217

theorem tailTrace_2932493 : CollatzResearch.WordTrace tailWord_2932493 prefixEnd_2932493 1505778424945300341351217 := by
  unfold tailWord_2932493
  simp only [CollatzResearch.WordTrace]
  refine ⟨106956806565086165776402133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71304537710057443850934755 106956806565086165776402133)
  ·
    refine ⟨2506800153869207010384425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106956806565086165776402133 2506800153869207010384425)
    ·
      refine ⟨1880100115401905257788319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2506800153869207010384425 1880100115401905257788319)
      ·
        refine ⟨2820150173102857886682479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880100115401905257788319 2820150173102857886682479)
        ·
          refine ⟨4230225259654286830023719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820150173102857886682479 4230225259654286830023719)
          ·
            refine ⟨6345337889481430245035579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230225259654286830023719 6345337889481430245035579)
            ·
              refine ⟨9518006834222145367553369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345337889481430245035579 9518006834222145367553369)
              ·
                refine ⟨7138505125666609025665027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9518006834222145367553369 7138505125666609025665027)
                ·
                  refine ⟨10707757688499913538497541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138505125666609025665027 10707757688499913538497541)
                  ·
                    refine ⟨2007704566593733788468289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10707757688499913538497541 2007704566593733788468289)
                    ·
                      refine ⟨1505778424945300341351217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007704566593733788468289 1505778424945300341351217)
                      ·
                        rfl

theorem cell23_2932493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2932493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932493 prefixEnd_2932493 := by exact prefixLift 2932493
  have htrace : WordTrace (prefixWord ++ tailWord_2932493) baseStart_2932493 baseEnd_2932493 := by
    simpa [prefixWord, tailWord_2932493, baseEnd_2932493] using wordTrace_append hprefix tailTrace_2932493
  have hstable : (prefixWord ++ tailWord_2932493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932493).length < 2 ^ (prefixWord ++ tailWord_2932493).sum := by decide
  have hdescent : baseEnd_2932493 < baseStart_2932493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932532 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_2932532 : Nat := 118140960795 + 2932532 * 2 ^ 59
def prefixEnd_2932532 : Nat := 4983230072969 + 3 ^ 40 * 2932532 * 2
def baseEnd_2932532 : Nat := 1505798450690825688763537

theorem tailTrace_2932532 : CollatzResearch.WordTrace tailWord_2932532 prefixEnd_2932532 1505798450690825688763537 := by
  unfold tailWord_2932532
  simp only [CollatzResearch.WordTrace]
  refine ⟨53479114505972437718535925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71305486007963250291381233 53479114505972437718535925)
  ·
    refine ⟨5013666984934916036112743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53479114505972437718535925 5013666984934916036112743)
    ·
      refine ⟨7520500477402374054169115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013666984934916036112743 7520500477402374054169115)
      ·
        refine ⟨11280750716103561081253673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7520500477402374054169115 11280750716103561081253673)
        ·
          refine ⟨8460563037077670810940255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11280750716103561081253673 8460563037077670810940255)
          ·
            refine ⟨12690844555616506216410383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8460563037077670810940255 12690844555616506216410383)
            ·
              refine ⟨19036266833424759324615575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12690844555616506216410383 19036266833424759324615575)
              ·
                refine ⟨28554400250137138986923363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19036266833424759324615575 28554400250137138986923363)
                ·
                  refine ⟨42831600375205708480385045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28554400250137138986923363 42831600375205708480385045)
                  ·
                    refine ⟨2007731267587767585018049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42831600375205708480385045 2007731267587767585018049)
                    ·
                      refine ⟨1505798450690825688763537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007731267587767585018049 1505798450690825688763537)
                      ·
                        rfl

theorem cell23_2932532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_2932532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932532 prefixEnd_2932532 := by exact prefixLift 2932532
  have htrace : WordTrace (prefixWord ++ tailWord_2932532) baseStart_2932532 baseEnd_2932532 := by
    simpa [prefixWord, tailWord_2932532, baseEnd_2932532] using wordTrace_append hprefix tailTrace_2932532
  have hstable : (prefixWord ++ tailWord_2932532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932532).length < 2 ^ (prefixWord ++ tailWord_2932532).sum := by decide
  have hdescent : baseEnd_2932532 < baseStart_2932532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932542 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2932542 : Nat := 118140960795 + 2932542 * 2 ^ 59
def prefixEnd_2932542 : Nat := 4983230072969 + 3 ^ 40 * 2932542 * 2
def baseEnd_2932542 : Nat := 501934528499123549879497

theorem tailTrace_2932542 : CollatzResearch.WordTrace tailWord_2932542 prefixEnd_2932542 501934528499123549879497 := by
  unfold tailWord_2932542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13369824217738580893116985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71305729161272431429957253 13369824217738580893116985)
  ·
    refine ⟨10027368163303935669837739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13369824217738580893116985 10027368163303935669837739)
    ·
      refine ⟨15041052244955903504756609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027368163303935669837739 15041052244955903504756609)
      ·
        refine ⟨11280789183716927628567457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15041052244955903504756609 11280789183716927628567457)
        ·
          refine ⟨8460591887787695721425593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11280789183716927628567457 8460591887787695721425593)
          ·
            refine ⟨6345443915840771791069195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8460591887787695721425593 6345443915840771791069195)
            ·
              refine ⟨9518165873761157686603793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345443915840771791069195 9518165873761157686603793)
              ·
                refine ⟨7138624405320868264952845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9518165873761157686603793 7138624405320868264952845)
                ·
                  refine ⟨2676984151995325599357317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7138624405320868264952845 2676984151995325599357317)
                  ·
                    refine ⟨501934528499123549879497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2676984151995325599357317 501934528499123549879497)
                    ·
                      rfl

theorem cell23_2932542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2932542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932542 prefixEnd_2932542 := by exact prefixLift 2932542
  have htrace : WordTrace (prefixWord ++ tailWord_2932542) baseStart_2932542 baseEnd_2932542 := by
    simpa [prefixWord, tailWord_2932542, baseEnd_2932542] using wordTrace_append hprefix tailTrace_2932542
  have hstable : (prefixWord ++ tailWord_2932542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932542).length < 2 ^ (prefixWord ++ tailWord_2932542).sum := by decide
  have hdescent : baseEnd_2932542 < baseStart_2932542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932552 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_2932552 : Nat := 118140960795 + 2932552 * 2 ^ 59
def prefixEnd_2932552 : Nat := 4983230072969 + 3 ^ 40 * 2932552 * 2
def baseEnd_2932552 : Nat := 1505808720303915610513445

theorem tailTrace_2932552 : CollatzResearch.WordTrace tailWord_2932552 prefixEnd_2932552 1505808720303915610513445 := by
  unfold tailWord_2932552
  simp only [CollatzResearch.WordTrace]
  refine ⟨53479479235936209426399955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71305972314581612568533273 53479479235936209426399955)
  ·
    refine ⟨80219218853904314139599933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53479479235936209426399955 80219218853904314139599933)
    ·
      refine ⟨30082207070214117802349975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80219218853904314139599933 30082207070214117802349975)
      ·
        refine ⟨45123310605321176703524963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30082207070214117802349975 45123310605321176703524963)
        ·
          refine ⟨67684965907981765055287445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45123310605321176703524963 67684965907981765055287445)
          ·
            refine ⟨3172732776936645236966599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67684965907981765055287445 3172732776936645236966599)
            ·
              refine ⟨4759099165404967855449899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172732776936645236966599 4759099165404967855449899)
              ·
                refine ⟨7138648748107451783174849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759099165404967855449899 7138648748107451783174849)
                ·
                  refine ⟨5353986561080588837381137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138648748107451783174849 5353986561080588837381137)
                  ·
                    refine ⟨4015489920810441628035853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5353986561080588837381137 4015489920810441628035853)
                    ·
                      refine ⟨1505808720303915610513445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015489920810441628035853 1505808720303915610513445)
                      ·
                        rfl

theorem cell23_2932552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_2932552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932552 prefixEnd_2932552 := by exact prefixLift 2932552
  have htrace : WordTrace (prefixWord ++ tailWord_2932552) baseStart_2932552 baseEnd_2932552 := by
    simpa [prefixWord, tailWord_2932552, baseEnd_2932552] using wordTrace_append hprefix tailTrace_2932552
  have hstable : (prefixWord ++ tailWord_2932552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932552).length < 2 ^ (prefixWord ++ tailWord_2932552).sum := by decide
  have hdescent : baseEnd_2932552 < baseStart_2932552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932605 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_2932605 : Nat := 118140960795 + 2932605 * 2 ^ 59
def prefixEnd_2932605 : Nat := 4983230072969 + 3 ^ 40 * 2932605 * 2
def baseEnd_2932605 : Nat := 1505835934778603903150701

theorem tailTrace_2932605 : CollatzResearch.WordTrace tailWord_2932605 prefixEnd_2932605 1505835934778603903150701 := by
  unfold tailWord_2932605
  simp only [CollatzResearch.WordTrace]
  refine ⟨106960891540680408904479269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71307261027120272602986179 106960891540680408904479269)
  ·
    refine ⟨20055167163877576669589863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106960891540680408904479269 20055167163877576669589863)
    ·
      refine ⟨30082750745816365004384795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20055167163877576669589863 30082750745816365004384795)
      ·
        refine ⟨45124126118724547506577193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30082750745816365004384795 45124126118724547506577193)
        ·
          refine ⟨33843094589043410629932895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45124126118724547506577193 33843094589043410629932895)
          ·
            refine ⟨50764641883565115944899343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33843094589043410629932895 50764641883565115944899343)
            ·
              refine ⟨76146962825347673917349015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50764641883565115944899343 76146962825347673917349015)
              ·
                refine ⟨114220444238021510876023523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76146962825347673917349015 114220444238021510876023523)
                ·
                  refine ⟨171330666357032266314035285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114220444238021510876023523 171330666357032266314035285)
                  ·
                    refine ⟨2007781246371471870867601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 171330666357032266314035285 2007781246371471870867601)
                    ·
                      refine ⟨1505835934778603903150701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007781246371471870867601 1505835934778603903150701)
                      ·
                        rfl

theorem cell23_2932605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_2932605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932605 prefixEnd_2932605 := by exact prefixLift 2932605
  have htrace : WordTrace (prefixWord ++ tailWord_2932605) baseStart_2932605 baseEnd_2932605 := by
    simpa [prefixWord, tailWord_2932605, baseEnd_2932605] using wordTrace_append hprefix tailTrace_2932605
  have hstable : (prefixWord ++ tailWord_2932605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932605).length < 2 ^ (prefixWord ++ tailWord_2932605).sum := by decide
  have hdescent : baseEnd_2932605 < baseStart_2932605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932608 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2932608 : Nat := 118140960795 + 2932608 * 2 ^ 59
def prefixEnd_2932608 : Nat := 4983230072969 + 3 ^ 40 * 2932608 * 2
def baseEnd_2932608 : Nat := 1505837475220567391413187

theorem tailTrace_2932608 : CollatzResearch.WordTrace tailWord_2932608 prefixEnd_2932608 1505837475220567391413187 := by
  unfold tailWord_2932608
  simp only [CollatzResearch.WordTrace]
  refine ⟨53480500479834770208419239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71307333973113026944558985 53480500479834770208419239)
  ·
    refine ⟨80220750719752155312628859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53480500479834770208419239 80220750719752155312628859)
    ·
      refine ⟨120331126079628232968943289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80220750719752155312628859 120331126079628232968943289)
      ·
        refine ⟨90248344559721174726707467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120331126079628232968943289 90248344559721174726707467)
        ·
          refine ⟨135372516839581762090061201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90248344559721174726707467 135372516839581762090061201)
          ·
            refine ⟨101529387629686321567545901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135372516839581762090061201 101529387629686321567545901)
            ·
              refine ⟨38073520361132370587829713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101529387629686321567545901 38073520361132370587829713)
              ·
                refine ⟨28555140270849277940872285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38073520361132370587829713 28555140270849277940872285)
                ·
                  refine ⟨10708177601568479227827107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28555140270849277940872285 10708177601568479227827107)
                  ·
                    refine ⟨16062266402352718841740661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10708177601568479227827107 16062266402352718841740661)
                    ·
                      refine ⟨1505837475220567391413187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16062266402352718841740661 1505837475220567391413187)
                      ·
                        rfl

theorem cell23_2932608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2932608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932608 prefixEnd_2932608 := by exact prefixLift 2932608
  have htrace : WordTrace (prefixWord ++ tailWord_2932608) baseStart_2932608 baseEnd_2932608 := by
    simpa [prefixWord, tailWord_2932608, baseEnd_2932608] using wordTrace_append hprefix tailTrace_2932608
  have hstable : (prefixWord ++ tailWord_2932608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932608).length < 2 ^ (prefixWord ++ tailWord_2932608).sum := by decide
  have hdescent : baseEnd_2932608 < baseStart_2932608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932655 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_2932655 : Nat := 118140960795 + 2932655 * 2 ^ 59
def prefixEnd_2932655 : Nat := 4983230072969 + 3 ^ 40 * 2932655 * 2
def baseEnd_2932655 : Nat := 1505861608811328707525471

theorem tailTrace_2932655 : CollatzResearch.WordTrace tailWord_2932655 prefixEnd_2932655 1505861608811328707525471 := by
  unfold tailWord_2932655
  simp only [CollatzResearch.WordTrace]
  refine ⟨106962715190499267443799419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71308476793666178295866279 106962715190499267443799419)
  ·
    refine ⟨160444072785748901165699129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106962715190499267443799419 160444072785748901165699129)
    ·
      refine ⟨120333054589311675874274347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160444072785748901165699129 120333054589311675874274347)
      ·
        refine ⟨180499581883967513811411521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120333054589311675874274347 180499581883967513811411521)
        ·
          refine ⟨135374686412975635358558641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180499581883967513811411521 135374686412975635358558641)
          ·
            refine ⟨101531014809731726518918981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135374686412975635358558641 101531014809731726518918981)
            ·
              refine ⟨19037065276824698722297309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101531014809731726518918981 19037065276824698722297309)
              ·
                refine ⟨7138899478809262020861491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19037065276824698722297309 7138899478809262020861491)
                ·
                  refine ⟨10708349218213893031292237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138899478809262020861491 10708349218213893031292237)
                  ·
                    refine ⟨4015630956830209886734589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10708349218213893031292237 4015630956830209886734589)
                    ·
                      refine ⟨1505861608811328707525471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015630956830209886734589 1505861608811328707525471)
                      ·
                        rfl

theorem cell23_2932655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_2932655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932655 prefixEnd_2932655 := by exact prefixLift 2932655
  have htrace : WordTrace (prefixWord ++ tailWord_2932655) baseStart_2932655 baseEnd_2932655 := by
    simpa [prefixWord, tailWord_2932655, baseEnd_2932655] using wordTrace_append hprefix tailTrace_2932655
  have hstable : (prefixWord ++ tailWord_2932655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932655).length < 2 ^ (prefixWord ++ tailWord_2932655).sum := by decide
  have hdescent : baseEnd_2932655 < baseStart_2932655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932706 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2932706 : Nat := 118140960795 + 2932706 * 2 ^ 59
def prefixEnd_2932706 : Nat := 4983230072969 + 3 ^ 40 * 2932706 * 2
def baseEnd_2932706 : Nat := 1505887796324708007987737

theorem tailTrace_2932706 : CollatzResearch.WordTrace tailWord_2932706 prefixEnd_2932706 1505887796324708007987737 := by
  unfold tailWord_2932706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741143828328625788476493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71309716875543002102603981 26741143828328625788476493)
  ·
    refine ⟨10027928935623234670678685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26741143828328625788476493 10027928935623234670678685)
    ·
      refine ⟨3760473350858713001504507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10027928935623234670678685 3760473350858713001504507)
      ·
        refine ⟨5640710026288069502256761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760473350858713001504507 5640710026288069502256761)
        ·
          refine ⟨4230532519716052126692571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640710026288069502256761 4230532519716052126692571)
          ·
            refine ⟨6345798779574078190038857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230532519716052126692571 6345798779574078190038857)
            ·
              refine ⟨4759349084680558642529143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6345798779574078190038857 4759349084680558642529143)
              ·
                refine ⟨7139023627020837963793715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759349084680558642529143 7139023627020837963793715)
                ·
                  refine ⟨10708535440531256945690573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139023627020837963793715 10708535440531256945690573)
                  ·
                    refine ⟨4015700790199221354633965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10708535440531256945690573 4015700790199221354633965)
                    ·
                      refine ⟨1505887796324708007987737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015700790199221354633965 1505887796324708007987737)
                      ·
                        rfl

theorem cell23_2932706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2932706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932706 prefixEnd_2932706 := by exact prefixLift 2932706
  have htrace : WordTrace (prefixWord ++ tailWord_2932706) baseStart_2932706 baseEnd_2932706 := by
    simpa [prefixWord, tailWord_2932706, baseEnd_2932706] using wordTrace_append hprefix tailTrace_2932706
  have hstable : (prefixWord ++ tailWord_2932706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932706).length < 2 ^ (prefixWord ++ tailWord_2932706).sum := by decide
  have hdescent : baseEnd_2932706 < baseStart_2932706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932740 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2932740 : Nat := 118140960795 + 2932740 * 2 ^ 59
def prefixEnd_2932740 : Nat := 4983230072969 + 3 ^ 40 * 2932740 * 2
def baseEnd_2932740 : Nat := 1505905254666960874962581

theorem tailTrace_2932740 : CollatzResearch.WordTrace tailWord_2932740 prefixEnd_2932740 1505905254666960874962581 := by
  unfold tailWord_2932740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53482907697595663480321837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71310543596794217973762449 53482907697595663480321837)
  ·
    refine ⟨20056090386598373805120689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53482907697595663480321837 20056090386598373805120689)
    ·
      refine ⟨15042067789948780353840517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20056090386598373805120689 15042067789948780353840517)
      ·
        refine ⟨2820387710615396316345097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15042067789948780353840517 2820387710615396316345097)
        ·
          refine ⟨2115290782961547237258823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820387710615396316345097 2115290782961547237258823)
          ·
            refine ⟨3172936174442320855888235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115290782961547237258823 3172936174442320855888235)
            ·
              refine ⟨4759404261663481283832353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3172936174442320855888235 4759404261663481283832353)
              ·
                refine ⟨3569553196247610962874265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759404261663481283832353 3569553196247610962874265)
                ·
                  refine ⟨2677164897185708222155699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569553196247610962874265 2677164897185708222155699)
                  ·
                    refine ⟨4015747345778562333233549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2677164897185708222155699 4015747345778562333233549)
                    ·
                      refine ⟨1505905254666960874962581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015747345778562333233549 1505905254666960874962581)
                      ·
                        rfl

theorem cell23_2932740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2932740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932740 prefixEnd_2932740 := by exact prefixLift 2932740
  have htrace : WordTrace (prefixWord ++ tailWord_2932740) baseStart_2932740 baseEnd_2932740 := by
    simpa [prefixWord, tailWord_2932740, baseEnd_2932740] using wordTrace_append hprefix tailTrace_2932740
  have hstable : (prefixWord ++ tailWord_2932740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932740).length < 2 ^ (prefixWord ++ tailWord_2932740).sum := by decide
  have hdescent : baseEnd_2932740 < baseStart_2932740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932746 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2932746 : Nat := 118140960795 + 2932746 * 2 ^ 59
def prefixEnd_2932746 : Nat := 4983230072969 + 3 ^ 40 * 2932746 * 2
def baseEnd_2932746 : Nat := 1505908335550887851487553

theorem tailTrace_2932746 : CollatzResearch.WordTrace tailWord_2932746 prefixEnd_2932746 1505908335550887851487553 := by
  unfold tailWord_2932746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741508558292397496340523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71310689488779726656908061 26741508558292397496340523)
  ·
    refine ⟨40112262837438596244510785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26741508558292397496340523 40112262837438596244510785)
    ·
      refine ⟨30084197128078947183383089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40112262837438596244510785 30084197128078947183383089)
      ·
        refine ⟨22563147846059210387537317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30084197128078947183383089 22563147846059210387537317)
        ·
          refine ⟨4230590221136101947663247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22563147846059210387537317 4230590221136101947663247)
          ·
            refine ⟨6345885331704152921494871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230590221136101947663247 6345885331704152921494871)
            ·
              refine ⟨9518827997556229382242307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345885331704152921494871 9518827997556229382242307)
              ·
                refine ⟨14278241996334344073363461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518827997556229382242307 14278241996334344073363461)
                ·
                  refine ⟨2677170374312689513755649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14278241996334344073363461 2677170374312689513755649)
                  ·
                    refine ⟨2007877780734517135316737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677170374312689513755649 2007877780734517135316737)
                    ·
                      refine ⟨1505908335550887851487553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007877780734517135316737 1505908335550887851487553)
                      ·
                        rfl

theorem cell23_2932746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2932746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932746 prefixEnd_2932746 := by exact prefixLift 2932746
  have htrace : WordTrace (prefixWord ++ tailWord_2932746) baseStart_2932746 baseEnd_2932746 := by
    simpa [prefixWord, tailWord_2932746, baseEnd_2932746] using wordTrace_append hprefix tailTrace_2932746
  have hstable : (prefixWord ++ tailWord_2932746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932746).length < 2 ^ (prefixWord ++ tailWord_2932746).sum := by decide
  have hdescent : baseEnd_2932746 < baseStart_2932746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932762 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_2932762 : Nat := 118140960795 + 2932762 * 2 ^ 59
def prefixEnd_2932762 : Nat := 4983230072969 + 3 ^ 40 * 2932762 * 2
def baseEnd_2932762 : Nat := 1505916551241359788887479

theorem tailTrace_2932762 : CollatzResearch.WordTrace tailWord_2932762 prefixEnd_2932762 1505916551241359788887479 := by
  unfold tailWord_2932762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741654450277906179486135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71311078534074416478629693 26741654450277906179486135)
  ·
    refine ⟨40112481675416859269229203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26741654450277906179486135 40112481675416859269229203)
    ·
      refine ⟨60168722513125288903843805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40112481675416859269229203 60168722513125288903843805)
      ·
        refine ⟨22563270942421983338941427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60168722513125288903843805 22563270942421983338941427)
        ·
          refine ⟨33844906413632975008412141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22563270942421983338941427 33844906413632975008412141)
          ·
            refine ⟨12691839905112365628154553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33844906413632975008412141 12691839905112365628154553)
            ·
              refine ⟨9518879928834274221115915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12691839905112365628154553 9518879928834274221115915)
              ·
                refine ⟨14278319893251411331673873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518879928834274221115915 14278319893251411331673873)
                ·
                  refine ⟨10708739919938558498755405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14278319893251411331673873 10708739919938558498755405)
                  ·
                    refine ⟨4015777469976959437033277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10708739919938558498755405 4015777469976959437033277)
                    ·
                      refine ⟨1505916551241359788887479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015777469976959437033277 1505916551241359788887479)
                      ·
                        rfl

theorem cell23_2932762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_2932762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932762 prefixEnd_2932762 := by exact prefixLift 2932762
  have htrace : WordTrace (prefixWord ++ tailWord_2932762) baseStart_2932762 baseEnd_2932762 := by
    simpa [prefixWord, tailWord_2932762, baseEnd_2932762] using wordTrace_append hprefix tailTrace_2932762
  have hstable : (prefixWord ++ tailWord_2932762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932762).length < 2 ^ (prefixWord ++ tailWord_2932762).sum := by decide
  have hdescent : baseEnd_2932762 < baseStart_2932762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932782 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2932782 : Nat := 118140960795 + 2932782 * 2 ^ 59
def prefixEnd_2932782 : Nat := 4983230072969 + 3 ^ 40 * 2932782 * 2
def baseEnd_2932782 : Nat := 501975606951483236879129

theorem tailTrace_2932782 : CollatzResearch.WordTrace tailWord_2932782 prefixEnd_2932782 501975606951483236879129 := by
  unfold tailWord_2932782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370918407629896016709075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71311564840692778755781733 13370918407629896016709075)
  ·
    refine ⟨20056377611444844025063613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370918407629896016709075 20056377611444844025063613)
    ·
      refine ⟨7521141604291816509398855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20056377611444844025063613 7521141604291816509398855)
      ·
        refine ⟨11281712406437724764098283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521141604291816509398855 11281712406437724764098283)
        ·
          refine ⟨16922568609656587146147425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281712406437724764098283 16922568609656587146147425)
          ·
            refine ⟨12691926457242440359610569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16922568609656587146147425 12691926457242440359610569)
            ·
              refine ⟨9518944842931830269707927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12691926457242440359610569 9518944842931830269707927)
              ·
                refine ⟨14278417264397745404561891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518944842931830269707927 14278417264397745404561891)
                ·
                  refine ⟨21417625896596618106842837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14278417264397745404561891 21417625896596618106842837)
                  ·
                    refine ⟨501975606951483236879129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21417625896596618106842837 501975606951483236879129)
                    ·
                      rfl

theorem cell23_2932782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2932782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932782 prefixEnd_2932782 := by exact prefixLift 2932782
  have htrace : WordTrace (prefixWord ++ tailWord_2932782) baseStart_2932782 baseEnd_2932782 := by
    simpa [prefixWord, tailWord_2932782, baseEnd_2932782] using wordTrace_append hprefix tailTrace_2932782
  have hstable : (prefixWord ++ tailWord_2932782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932782).length < 2 ^ (prefixWord ++ tailWord_2932782).sum := by decide
  have hdescent : baseEnd_2932782 < baseStart_2932782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932806 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2932806 : Nat := 118140960795 + 2932806 * 2 ^ 59
def prefixEnd_2932806 : Nat := 4983230072969 + 3 ^ 40 * 2932806 * 2
def baseEnd_2932806 : Nat := 1505939144390157616737277

theorem tailTrace_2932806 : CollatzResearch.WordTrace tailWord_2932806 prefixEnd_2932806 1505939144390157616737277 := by
  unfold tailWord_2932806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3342756956654756882267071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71312148408634813488364181 3342756956654756882267071)
  ·
    refine ⟨5014135434982135323400607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3342756956654756882267071 5014135434982135323400607)
    ·
      refine ⟨7521203152473202985100911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014135434982135323400607 7521203152473202985100911)
      ·
        refine ⟨11281804728709804477651367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521203152473202985100911 11281804728709804477651367)
        ·
          refine ⟨16922707093064706716477051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281804728709804477651367 16922707093064706716477051)
          ·
            refine ⟨25384060639597060074715577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16922707093064706716477051 25384060639597060074715577)
            ·
              refine ⟨19038045479697795056036683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25384060639597060074715577 19038045479697795056036683)
              ·
                refine ⟨28557068219546692584055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19038045479697795056036683 28557068219546692584055025)
                ·
                  refine ⟨21417801164660019438041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28557068219546692584055025 21417801164660019438041269)
                  ·
                    refine ⟨2007918859186876822316369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21417801164660019438041269 2007918859186876822316369)
                    ·
                      refine ⟨1505939144390157616737277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007918859186876822316369 1505939144390157616737277)
                      ·
                        rfl

theorem cell23_2932806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2932806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932806 prefixEnd_2932806 := by exact prefixLift 2932806
  have htrace : WordTrace (prefixWord ++ tailWord_2932806) baseStart_2932806 baseEnd_2932806 := by
    simpa [prefixWord, tailWord_2932806, baseEnd_2932806] using wordTrace_append hprefix tailTrace_2932806
  have hstable : (prefixWord ++ tailWord_2932806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932806).length < 2 ^ (prefixWord ++ tailWord_2932806).sum := by decide
  have hdescent : baseEnd_2932806 < baseStart_2932806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932839 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2932839 : Nat := 118140960795 + 2932839 * 2 ^ 59
def prefixEnd_2932839 : Nat := 4983230072969 + 3 ^ 40 * 2932839 * 2
def baseEnd_2932839 : Nat := 1505956089251755987624625

theorem tailTrace_2932839 : CollatzResearch.WordTrace tailWord_2932839 prefixEnd_2932839 1505956089251755987624625 := by
  unfold tailWord_2932839
  simp only [CollatzResearch.WordTrace]
  refine ⟨106969426221832666868497571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71312950814555111245665047 106969426221832666868497571)
  ·
    refine ⟨160454139332749000302746357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106969426221832666868497571 160454139332749000302746357)
    ·
      refine ⟨15042575562445218778382471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160454139332749000302746357 15042575562445218778382471)
      ·
        refine ⟨22563863343667828167573707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15042575562445218778382471 22563863343667828167573707)
        ·
          refine ⟨33845795015501742251360561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22563863343667828167573707 33845795015501742251360561)
          ·
            refine ⟨25384346261626306688520421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33845795015501742251360561 25384346261626306688520421)
            ·
              refine ⟨4759564924054932504097579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25384346261626306688520421 4759564924054932504097579)
              ·
                refine ⟨7139347386082398756146369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759564924054932504097579 7139347386082398756146369)
                ·
                  refine ⟨5354510539561799067109777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139347386082398756146369 5354510539561799067109777)
                  ·
                    refine ⟨4015882904671349300332333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354510539561799067109777 4015882904671349300332333)
                    ·
                      refine ⟨1505956089251755987624625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4015882904671349300332333 1505956089251755987624625)
                      ·
                        rfl

theorem cell23_2932839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2932839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932839 prefixEnd_2932839 := by exact prefixLift 2932839
  have htrace : WordTrace (prefixWord ++ tailWord_2932839) baseStart_2932839 baseEnd_2932839 := by
    simpa [prefixWord, tailWord_2932839, baseEnd_2932839] using wordTrace_append hprefix tailTrace_2932839
  have hstable : (prefixWord ++ tailWord_2932839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932839).length < 2 ^ (prefixWord ++ tailWord_2932839).sum := by decide
  have hdescent : baseEnd_2932839 < baseStart_2932839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932846 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2932846 : Nat := 118140960795 + 2932846 * 2 ^ 59
def prefixEnd_2932846 : Nat := 4983230072969 + 3 ^ 40 * 2932846 * 2
def baseEnd_2932846 : Nat := 501986561205445820079031

theorem tailTrace_2932846 : CollatzResearch.WordTrace tailWord_2932846 prefixEnd_2932846 501986561205445820079031 := by
  unfold tailWord_2932846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371210191600913383000299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71313121021871538042668261 13371210191600913383000299)
  ·
    refine ⟨20056815287401370074500449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371210191600913383000299 20056815287401370074500449)
    ·
      refine ⟨15042611465551027555875337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20056815287401370074500449 15042611465551027555875337)
      ·
        refine ⟨11281958599163270666906503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15042611465551027555875337 11281958599163270666906503)
        ·
          refine ⟨16922937898744906000359755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281958599163270666906503 16922937898744906000359755)
          ·
            refine ⟨25384406848117359000539633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16922937898744906000359755 25384406848117359000539633)
            ·
              refine ⟨19038305136088019250404725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25384406848117359000539633 19038305136088019250404725)
              ·
                refine ⟨1784841106508251804725443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19038305136088019250404725 1784841106508251804725443)
                ·
                  refine ⟨2677261659762377707088165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784841106508251804725443 2677261659762377707088165)
                  ·
                    refine ⟨501986561205445820079031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677261659762377707088165 501986561205445820079031)
                    ·
                      rfl

theorem cell23_2932846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2932846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932846 prefixEnd_2932846 := by exact prefixLift 2932846
  have htrace : WordTrace (prefixWord ++ tailWord_2932846) baseStart_2932846 baseEnd_2932846 := by
    simpa [prefixWord, tailWord_2932846, baseEnd_2932846] using wordTrace_append hprefix tailTrace_2932846
  have hstable : (prefixWord ++ tailWord_2932846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932846).length < 2 ^ (prefixWord ++ tailWord_2932846).sum := by decide
  have hdescent : baseEnd_2932846 < baseStart_2932846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932882 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2932882 : Nat := 118140960795 + 2932882 * 2 ^ 59
def prefixEnd_2932882 : Nat := 4983230072969 + 3 ^ 40 * 2932882 * 2
def baseEnd_2932882 : Nat := 1505978168919899319386927

theorem tailTrace_2932882 : CollatzResearch.WordTrace tailWord_2932882 prefixEnd_2932882 1505978168919899319386927 := by
  unfold tailWord_2932882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26742748640169221303078225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71313996373784590141541933 26742748640169221303078225)
  ·
    refine ⟨20057061480126915977308669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26742748640169221303078225 20057061480126915977308669)
    ·
      refine ⟨7521398055047593491490751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20057061480126915977308669 7521398055047593491490751)
      ·
        refine ⟨11282097082571390237236127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7521398055047593491490751 11282097082571390237236127)
        ·
          refine ⟨16923145623857085355854191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11282097082571390237236127 16923145623857085355854191)
          ·
            refine ⟨25384718435785628033781287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16923145623857085355854191 25384718435785628033781287)
            ·
              refine ⟨38077077653678442050671931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25384718435785628033781287 38077077653678442050671931)
              ·
                refine ⟨57115616480517663076007897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38077077653678442050671931 57115616480517663076007897)
                ·
                  refine ⟨42836712360388247307005923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57115616480517663076007897 42836712360388247307005923)
                  ·
                    refine ⟨64255068540582370960508885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42836712360388247307005923 64255068540582370960508885)
                    ·
                      refine ⟨1505978168919899319386927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64255068540582370960508885 1505978168919899319386927)
                      ·
                        rfl

theorem cell23_2932882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2932882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932882 prefixEnd_2932882 := by exact prefixLift 2932882
  have htrace : WordTrace (prefixWord ++ tailWord_2932882) baseStart_2932882 baseEnd_2932882 := by
    simpa [prefixWord, tailWord_2932882, baseEnd_2932882] using wordTrace_append hprefix tailTrace_2932882
  have hstable : (prefixWord ++ tailWord_2932882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932882).length < 2 ^ (prefixWord ++ tailWord_2932882).sum := by decide
  have hdescent : baseEnd_2932882 < baseStart_2932882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932896 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2]
def baseStart_2932896 : Nat := 118140960795 + 2932896 * 2 ^ 59
def prefixEnd_2932896 : Nat := 4983230072969 + 3 ^ 40 * 2932896 * 2
def baseEnd_2932896 : Nat := 1505985357649062264611863

theorem tailTrace_2932896 : CollatzResearch.WordTrace tailWord_2932896 prefixEnd_2932896 1505985357649062264611863 := by
  unfold tailWord_2932896
  simp only [CollatzResearch.WordTrace]
  refine ⟨53485752591313082801661271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71314336788417443735548361 53485752591313082801661271)
  ·
    refine ⟨80228628886969624202491907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53485752591313082801661271 80228628886969624202491907)
    ·
      refine ⟨120342943330454436303737861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80228628886969624202491907 120342943330454436303737861)
      ·
        refine ⟨22564301874460206806950849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120342943330454436303737861 22564301874460206806950849)
        ·
          refine ⟨16923226405845155105213137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22564301874460206806950849 16923226405845155105213137)
          ·
            refine ⟨12692419804383866328909853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16923226405845155105213137 12692419804383866328909853)
            ·
              refine ⟨4759657426643949873341195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12692419804383866328909853 4759657426643949873341195)
              ·
                refine ⟨7139486139965924810011793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759657426643949873341195 7139486139965924810011793)
                ·
                  refine ⟨5354614604974443607508845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139486139965924810011793 5354614604974443607508845)
                  ·
                    refine ⟨2007980476865416352815817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5354614604974443607508845 2007980476865416352815817)
                    ·
                      refine ⟨1505985357649062264611863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2007980476865416352815817 1505985357649062264611863)
                      ·
                        rfl

theorem cell23_2932896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_2932896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932896 prefixEnd_2932896 := by exact prefixLift 2932896
  have htrace : WordTrace (prefixWord ++ tailWord_2932896) baseStart_2932896 baseEnd_2932896 := by
    simpa [prefixWord, tailWord_2932896, baseEnd_2932896] using wordTrace_append hprefix tailTrace_2932896
  have hstable : (prefixWord ++ tailWord_2932896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932896).length < 2 ^ (prefixWord ++ tailWord_2932896).sum := by decide
  have hdescent : baseEnd_2932896 < baseStart_2932896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932910 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_2932910 : Nat := 118140960795 + 2932910 * 2 ^ 59
def prefixEnd_2932910 : Nat := 4983230072969 + 3 ^ 40 * 2932910 * 2
def baseEnd_2932910 : Nat := 167332505153136134426311

theorem tailTrace_2932910 : CollatzResearch.WordTrace tailWord_2932910 prefixEnd_2932910 167332505153136134426311 := by
  unfold tailWord_2932910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371501975571930749291523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71314677203050297329554789 13371501975571930749291523)
  ·
    refine ⟨20057252963357896123937285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371501975571930749291523 20057252963357896123937285)
    ·
      refine ⟨3760734930629605523238241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20057252963357896123937285 3760734930629605523238241)
      ·
        refine ⟨2820551197972204142428681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3760734930629605523238241 2820551197972204142428681)
        ·
          refine ⟨2115413398479153106821511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2820551197972204142428681 2115413398479153106821511)
          ·
            refine ⟨3173120097718729660232267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115413398479153106821511 3173120097718729660232267)
            ·
              refine ⟨4759680146578094490348401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173120097718729660232267 4759680146578094490348401)
              ·
                refine ⟨3569760109933570867761301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759680146578094490348401 3569760109933570867761301)
                ·
                  refine ⟨167332505153136134426311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3569760109933570867761301 167332505153136134426311)
                  ·
                    rfl

theorem cell23_2932910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_2932910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932910 prefixEnd_2932910 := by exact prefixLift 2932910
  have htrace : WordTrace (prefixWord ++ tailWord_2932910) baseStart_2932910 baseEnd_2932910 := by
    simpa [prefixWord, tailWord_2932910, baseEnd_2932910] using wordTrace_append hprefix tailTrace_2932910
  have hstable : (prefixWord ++ tailWord_2932910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932910).length < 2 ^ (prefixWord ++ tailWord_2932910).sum := by decide
  have hdescent : baseEnd_2932910 < baseStart_2932910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932919 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 4, 4]
def baseStart_2932919 : Nat := 118140960795 + 2932919 * 2 ^ 59
def prefixEnd_2932919 : Nat := 4983230072969 + 3 ^ 40 * 2932919 * 2
def baseEnd_2932919 : Nat := 501999055901371891541419

theorem tailTrace_2932919 : CollatzResearch.WordTrace tailWord_2932919 prefixEnd_2932919 501999055901371891541419 := by
  unfold tailWord_2932919
  simp only [CollatzResearch.WordTrace]
  refine ⟨106972344061542840531409811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71314896041028560354273207 106972344061542840531409811)
  ·
    refine ⟨160458516092314260797114717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106972344061542840531409811 160458516092314260797114717)
    ·
      refine ⟨60171943534617847798918019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160458516092314260797114717 60171943534617847798918019)
      ·
        refine ⟨90257915301926771698377029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60171943534617847798918019 90257915301926771698377029)
        ·
          refine ⟨16923359119111269693445693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90257915301926771698377029 16923359119111269693445693)
          ·
            refine ⟨6346259669666726135042135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16923359119111269693445693 6346259669666726135042135)
            ·
              refine ⟨9519389504500089202563203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346259669666726135042135 9519389504500089202563203)
              ·
                refine ⟨14279084256750133803844805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9519389504500089202563203 14279084256750133803844805)
                ·
                  refine ⟨2677328298140650088220901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14279084256750133803844805 2677328298140650088220901)
                  ·
                    refine ⟨501999055901371891541419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677328298140650088220901 501999055901371891541419)
                    ·
                      rfl

theorem cell23_2932919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_2932919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932919 prefixEnd_2932919 := by exact prefixLift 2932919
  have htrace : WordTrace (prefixWord ++ tailWord_2932919) baseStart_2932919 baseEnd_2932919 := by
    simpa [prefixWord, tailWord_2932919, baseEnd_2932919] using wordTrace_append hprefix tailTrace_2932919
  have hstable : (prefixWord ++ tailWord_2932919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932919).length < 2 ^ (prefixWord ++ tailWord_2932919).sum := by decide
  have hdescent : baseEnd_2932919 < baseStart_2932919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932922 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2932922 : Nat := 118140960795 + 2932922 * 2 ^ 59
def prefixEnd_2932922 : Nat := 4983230072969 + 3 ^ 40 * 2932922 * 2
def baseEnd_2932922 : Nat := 1505998708146079162886743

theorem tailTrace_2932922 : CollatzResearch.WordTrace tailWord_2932922 prefixEnd_2932922 1505998708146079162886743 := by
  unfold tailWord_2932922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743113370132993010942255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71314968987021314695846013 26743113370132993010942255)
  ·
    refine ⟨40114670055199489516413383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26743113370132993010942255 40114670055199489516413383)
    ·
      refine ⟨60172005082799234274620075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40114670055199489516413383 60172005082799234274620075)
      ·
        refine ⟨90258007624198851411930113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60172005082799234274620075 90258007624198851411930113)
        ·
          refine ⟨67693505718149138558947585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90258007624198851411930113 67693505718149138558947585)
          ·
            refine ⟨50770129288611853919210689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67693505718149138558947585 50770129288611853919210689)
            ·
              refine ⟨38077596966458890439408017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50770129288611853919210689 38077596966458890439408017)
              ·
                refine ⟨28558197724844167829556013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38077596966458890439408017 28558197724844167829556013)
                ·
                  refine ⟨10709324146816562936083505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28558197724844167829556013 10709324146816562936083505)
                  ·
                    refine ⟨8031993110112422202062629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10709324146816562936083505 8031993110112422202062629)
                    ·
                      refine ⟨1505998708146079162886743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8031993110112422202062629 1505998708146079162886743)
                      ·
                        rfl

theorem cell23_2932922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2932922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932922 prefixEnd_2932922 := by exact prefixLift 2932922
  have htrace : WordTrace (prefixWord ++ tailWord_2932922) baseStart_2932922 baseEnd_2932922 := by
    simpa [prefixWord, tailWord_2932922, baseEnd_2932922] using wordTrace_append hprefix tailTrace_2932922
  have hstable : (prefixWord ++ tailWord_2932922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932922).length < 2 ^ (prefixWord ++ tailWord_2932922).sum := by decide
  have hdescent : baseEnd_2932922 < baseStart_2932922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932946 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2932946 : Nat := 118140960795 + 2932946 * 2 ^ 59
def prefixEnd_2932946 : Nat := 4983230072969 + 3 ^ 40 * 2932946 * 2
def baseEnd_2932946 : Nat := 1506011031681787068986633

theorem tailTrace_2932946 : CollatzResearch.WordTrace tailWord_2932946 prefixEnd_2932946 1506011031681787068986633 := by
  unfold tailWord_2932946
  simp only [CollatzResearch.WordTrace]
  refine ⟨26743332208111256035660673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71315552554963349428428461 26743332208111256035660673)
  ·
    refine ⟨20057499156083442026745505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26743332208111256035660673 20057499156083442026745505)
    ·
      refine ⟨15043124367062581520059129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20057499156083442026745505 15043124367062581520059129)
      ·
        refine ⟨11282343275296936140044347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15043124367062581520059129 11282343275296936140044347)
        ·
          refine ⟨16923514912945404210066521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11282343275296936140044347 16923514912945404210066521)
          ·
            refine ⟨12692636184709053157549891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16923514912945404210066521 12692636184709053157549891)
            ·
              refine ⟨19038954277063579736324837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12692636184709053157549891 19038954277063579736324837)
              ·
                refine ⟨3569803926949421200560907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19038954277063579736324837 3569803926949421200560907)
                ·
                  refine ⟨5354705890424131800841361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569803926949421200560907 5354705890424131800841361)
                  ·
                    refine ⟨4016029417818098850631021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354705890424131800841361 4016029417818098850631021)
                    ·
                      refine ⟨1506011031681787068986633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016029417818098850631021 1506011031681787068986633)
                      ·
                        rfl

theorem cell23_2932946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2932946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932946 prefixEnd_2932946 := by exact prefixLift 2932946
  have htrace : WordTrace (prefixWord ++ tailWord_2932946) baseStart_2932946 baseEnd_2932946 := by
    simpa [prefixWord, tailWord_2932946, baseEnd_2932946] using wordTrace_append hprefix tailTrace_2932946
  have hstable : (prefixWord ++ tailWord_2932946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932946).length < 2 ^ (prefixWord ++ tailWord_2932946).sum := by decide
  have hdescent : baseEnd_2932946 < baseStart_2932946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932949 : List Nat := [1, 3, 2, 4, 2, 1, 1, 9]
def baseStart_2932949 : Nat := 118140960795 + 2932949 * 2 ^ 59
def prefixEnd_2932949 : Nat := 4983230072969 + 3 ^ 40 * 2932949 * 2
def baseEnd_2932949 : Nat := 55778243411990761379597

theorem tailTrace_2932949 : CollatzResearch.WordTrace tailWord_2932949 prefixEnd_2932949 55778243411990761379597 := by
  unfold tailWord_2932949
  simp only [CollatzResearch.WordTrace]
  refine ⟨106973438251434155655001901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71315625500956103770001267 106973438251434155655001901)
  ·
    refine ⟨40115039344287808370625713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106973438251434155655001901 40115039344287808370625713)
    ·
      refine ⟨30086279508215856277969285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40115039344287808370625713 30086279508215856277969285)
      ·
        refine ⟨5641177407790473052119241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30086279508215856277969285 5641177407790473052119241)
        ·
          refine ⟨4230883055842854789089431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5641177407790473052119241 4230883055842854789089431)
          ·
            refine ⟨6346324583764282183634147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230883055842854789089431 6346324583764282183634147)
            ·
              refine ⟨9519486875646423275451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346324583764282183634147 9519486875646423275451221)
              ·
                refine ⟨55778243411990761379597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9519486875646423275451221 55778243411990761379597)
                ·
                  rfl

theorem cell23_2932949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 9].length) (baseStart_2932949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932949 prefixEnd_2932949 := by exact prefixLift 2932949
  have htrace : WordTrace (prefixWord ++ tailWord_2932949) baseStart_2932949 baseEnd_2932949 := by
    simpa [prefixWord, tailWord_2932949, baseEnd_2932949] using wordTrace_append hprefix tailTrace_2932949
  have hstable : (prefixWord ++ tailWord_2932949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932949).length < 2 ^ (prefixWord ++ tailWord_2932949).sum := by decide
  have hdescent : baseEnd_2932949 < baseStart_2932949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932972 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2932972 : Nat := 118140960795 + 2932972 * 2 ^ 59
def prefixEnd_2932972 : Nat := 4983230072969 + 3 ^ 40 * 2932972 * 2
def baseEnd_2932972 : Nat := 1506024382178803967261513

theorem tailTrace_2932972 : CollatzResearch.WordTrace tailWord_2932972 prefixEnd_2932972 1506024382178803967261513 := by
  unfold tailWord_2932972
  simp only [CollatzResearch.WordTrace]
  refine ⟨53487138565175415291544585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71316184753567220388726113 53487138565175415291544585)
  ·
    refine ⟨40115353923881561468658439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53487138565175415291544585 40115353923881561468658439)
    ·
      refine ⟨60173030885822342202987659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40115353923881561468658439 60173030885822342202987659)
      ·
        refine ⟨90259546328733513304481489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60173030885822342202987659 90259546328733513304481489)
        ·
          refine ⟨67694659746550134978361117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90259546328733513304481489 67694659746550134978361117)
          ·
            refine ⟨25385497404956300616885419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67694659746550134978361117 25385497404956300616885419)
            ·
              refine ⟨38078246107434450925328129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385497404956300616885419 38078246107434450925328129)
              ·
                refine ⟨28558684580575838193996097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38078246107434450925328129 28558684580575838193996097)
                ·
                  refine ⟨21419013435431878645497073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28558684580575838193996097 21419013435431878645497073)
                  ·
                    refine ⟨16064260076573908984122805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21419013435431878645497073 16064260076573908984122805)
                    ·
                      refine ⟨1506024382178803967261513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16064260076573908984122805 1506024382178803967261513)
                      ·
                        rfl

theorem cell23_2932972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2932972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932972 prefixEnd_2932972 := by exact prefixLift 2932972
  have htrace : WordTrace (prefixWord ++ tailWord_2932972) baseStart_2932972 baseEnd_2932972 := by
    simpa [prefixWord, tailWord_2932972, baseEnd_2932972] using wordTrace_append hprefix tailTrace_2932972
  have hstable : (prefixWord ++ tailWord_2932972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932972).length < 2 ^ (prefixWord ++ tailWord_2932972).sum := by decide
  have hdescent : baseEnd_2932972 < baseStart_2932972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2932992 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_2932992 : Nat := 118140960795 + 2932992 * 2 ^ 59
def prefixEnd_2932992 : Nat := 4983230072969 + 3 ^ 40 * 2932992 * 2
def baseEnd_2932992 : Nat := 502011550597297963003807

theorem tailTrace_2932992 : CollatzResearch.WordTrace tailWord_2932992 prefixEnd_2932992 502011550597297963003807 := by
  unfold tailWord_2932992
  simp only [CollatzResearch.WordTrace]
  refine ⟨53487503295139186999408615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71316671060185582665878153 53487503295139186999408615)
  ·
    refine ⟨80231254942708780499112923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53487503295139186999408615 80231254942708780499112923)
    ·
      refine ⟨120346882414063170748669385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80231254942708780499112923 120346882414063170748669385)
      ·
        refine ⟨90260161810547378061502039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120346882414063170748669385 90260161810547378061502039)
        ·
          refine ⟨135390242715821067092253059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90260161810547378061502039 135390242715821067092253059)
          ·
            refine ⟨203085364073731600638379589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135390242715821067092253059 203085364073731600638379589)
            ·
              refine ⟨38078505763824675119696173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203085364073731600638379589 38078505763824675119696173)
              ·
                refine ⟨14279439661434253169886065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38078505763824675119696173 14279439661434253169886065)
                ·
                  refine ⟨10709579746075689877414549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14279439661434253169886065 10709579746075689877414549)
                  ·
                    refine ⟨502011550597297963003807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10709579746075689877414549 502011550597297963003807)
                    ·
                      rfl

theorem cell23_2932992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_2932992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2932992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2932992 prefixEnd_2932992 := by exact prefixLift 2932992
  have htrace : WordTrace (prefixWord ++ tailWord_2932992) baseStart_2932992 baseEnd_2932992 := by
    simpa [prefixWord, tailWord_2932992, baseEnd_2932992] using wordTrace_append hprefix tailTrace_2932992
  have hstable : (prefixWord ++ tailWord_2932992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2932992).length < 2 ^ (prefixWord ++ tailWord_2932992).sum := by decide
  have hdescent : baseEnd_2932992 < baseStart_2932992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2932992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933016 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_2933016 : Nat := 118140960795 + 2933016 * 2 ^ 59
def prefixEnd_2933016 : Nat := 4983230072969 + 3 ^ 40 * 2933016 * 2
def baseEnd_2933016 : Nat := 1506046975327601795111311

theorem tailTrace_2933016 : CollatzResearch.WordTrace tailWord_2933016 prefixEnd_2933016 1506046975327601795111311 := by
  unfold tailWord_2933016
  simp only [CollatzResearch.WordTrace]
  refine ⟨53487940971095713048845451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71317254628127617398460601 53487940971095713048845451)
  ·
    refine ⟨80231911456643569573268177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53487940971095713048845451 80231911456643569573268177)
    ·
      refine ⟨60173933592482677179951133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80231911456643569573268177 60173933592482677179951133)
      ·
        refine ⟨22565225097181003942481675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60173933592482677179951133 22565225097181003942481675)
        ·
          refine ⟨33847837645771505913722513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22565225097181003942481675 33847837645771505913722513)
          ·
            refine ⟨25385878234328629435291885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33847837645771505913722513 25385878234328629435291885)
            ·
              refine ⟨9519704337873236038234457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25385878234328629435291885 9519704337873236038234457)
              ·
                refine ⟨7139778253404927028675843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9519704337873236038234457 7139778253404927028675843)
                ·
                  refine ⟨10709667380107390543013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139778253404927028675843 10709667380107390543013765)
                  ·
                    refine ⟨2008062633770135726815081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10709667380107390543013765 2008062633770135726815081)
                    ·
                      refine ⟨1506046975327601795111311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008062633770135726815081 1506046975327601795111311)
                      ·
                        rfl

theorem cell23_2933016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_2933016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933016 prefixEnd_2933016 := by exact prefixLift 2933016
  have htrace : WordTrace (prefixWord ++ tailWord_2933016) baseStart_2933016 baseEnd_2933016 := by
    simpa [prefixWord, tailWord_2933016, baseEnd_2933016] using wordTrace_append hprefix tailTrace_2933016
  have hstable : (prefixWord ++ tailWord_2933016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933016).length < 2 ^ (prefixWord ++ tailWord_2933016).sum := by decide
  have hdescent : baseEnd_2933016 < baseStart_2933016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933084 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2933084 : Nat := 118140960795 + 2933084 * 2 ^ 59
def prefixEnd_2933084 : Nat := 4983230072969 + 3 ^ 40 * 2933084 * 2
def baseEnd_2933084 : Nat := 1506081892012107529060999

theorem tailTrace_2933084 : CollatzResearch.WordTrace tailWord_2933084 prefixEnd_2933084 1506081892012107529060999 := by
  unfold tailWord_2933084
  simp only [CollatzResearch.WordTrace]
  refine ⟨53489181052972536855583153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71318908070630049140777537 53489181052972536855583153)
  ·
    refine ⟨40116885789729402641687365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53489181052972536855583153 40116885789729402641687365)
    ·
      refine ⟨7521916085574262995316381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40116885789729402641687365 7521916085574262995316381)
      ·
        refine ⟨2820718532090348623243643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7521916085574262995316381 2820718532090348623243643)
        ·
          refine ⟨4231077798135522934865465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820718532090348623243643 4231077798135522934865465)
          ·
            refine ⟨3173308348601642201149099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231077798135522934865465 3173308348601642201149099)
            ·
              refine ⟨4759962522902463301723649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173308348601642201149099 4759962522902463301723649)
              ·
                refine ⟨3569971892176847476292737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4759962522902463301723649 3569971892176847476292737)
                ·
                  refine ⟨2677478919132635607219553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3569971892176847476292737 2677478919132635607219553)
                  ·
                    refine ⟨2008109189349476705414665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677478919132635607219553 2008109189349476705414665)
                    ·
                      refine ⟨1506081892012107529060999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008109189349476705414665 1506081892012107529060999)
                      ·
                        rfl

theorem cell23_2933084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2933084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933084 prefixEnd_2933084 := by exact prefixLift 2933084
  have htrace : WordTrace (prefixWord ++ tailWord_2933084) baseStart_2933084 baseEnd_2933084 := by
    simpa [prefixWord, tailWord_2933084, baseEnd_2933084] using wordTrace_append hprefix tailTrace_2933084
  have hstable : (prefixWord ++ tailWord_2933084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933084).length < 2 ^ (prefixWord ++ tailWord_2933084).sum := by decide
  have hdescent : baseEnd_2933084 < baseStart_2933084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933099 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 7, 4]
def baseStart_2933099 : Nat := 118140960795 + 2933099 * 2 ^ 59
def prefixEnd_2933099 : Nat := 4983230072969 + 3 ^ 40 * 2933099 * 2
def baseEnd_2933099 : Nat := 502029864740641656791143

theorem tailTrace_2933099 : CollatzResearch.WordTrace tailWord_2933099 prefixEnd_2933099 502029864740641656791143 := by
  unfold tailWord_2933099
  simp only [CollatzResearch.WordTrace]
  refine ⟨106978909200890731272962351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71319272800593820848641567 106978909200890731272962351)
  ·
    refine ⟨160468363801336096909443527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106978909200890731272962351 160468363801336096909443527)
    ·
      refine ⟨240702545702004145364165291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160468363801336096909443527 240702545702004145364165291)
      ·
        refine ⟨361053818553006218046247937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240702545702004145364165291 361053818553006218046247937)
        ·
          refine ⟨270790363914754663534685953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361053818553006218046247937 270790363914754663534685953)
          ·
            refine ⟨203092772936065997651014465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270790363914754663534685953 203092772936065997651014465)
            ·
              refine ⟨152319579702049498238260849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203092772936065997651014465 152319579702049498238260849)
              ·
                refine ⟨114239684776537123678695637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152319579702049498238260849 114239684776537123678695637)
                ·
                  refine ⟨2677492611950088836219429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114239684776537123678695637 2677492611950088836219429)
                  ·
                    refine ⟨502029864740641656791143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677492611950088836219429 502029864740641656791143)
                    ·
                      rfl

theorem cell23_2933099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 4].length) (baseStart_2933099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933099 prefixEnd_2933099 := by exact prefixLift 2933099
  have htrace : WordTrace (prefixWord ++ tailWord_2933099) baseStart_2933099 baseEnd_2933099 := by
    simpa [prefixWord, tailWord_2933099, baseEnd_2933099] using wordTrace_append hprefix tailTrace_2933099
  have hstable : (prefixWord ++ tailWord_2933099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933099).length < 2 ^ (prefixWord ++ tailWord_2933099).sum := by decide
  have hdescent : baseEnd_2933099 < baseStart_2933099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933129 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 8]
def baseStart_2933129 : Nat := 118140960795 + 2933129 * 2 ^ 59
def prefixEnd_2933129 : Nat := 4983230072969 + 3 ^ 40 * 2933129 * 2
def baseEnd_2933129 : Nat := 167344999849062205888699

theorem tailTrace_2933129 : CollatzResearch.WordTrace tailWord_2933129 prefixEnd_2933129 167344999849062205888699 := by
  unfold tailWord_2933129
  simp only [CollatzResearch.WordTrace]
  refine ⟨106980003390782046396554441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71320002260521364264369627 106980003390782046396554441)
  ·
    refine ⟨80235002543086534797415831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106980003390782046396554441 80235002543086534797415831)
    ·
      refine ⟨120352503814629802196123747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80235002543086534797415831 120352503814629802196123747)
      ·
        refine ⟨180528755721944703294185621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120352503814629802196123747 180528755721944703294185621)
        ·
          refine ⟨8462285424466157966914951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180528755721944703294185621 8462285424466157966914951)
          ·
            refine ⟨12693428136699236950372427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462285424466157966914951 12693428136699236950372427)
            ·
              refine ⟨19040142205048855425558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12693428136699236950372427 19040142205048855425558641)
              ·
                refine ⟨14280106653786641569168981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19040142205048855425558641 14280106653786641569168981)
                ·
                  refine ⟨167344999849062205888699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14280106653786641569168981 167344999849062205888699)
                  ·
                    rfl

theorem cell23_2933129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_2933129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933129 prefixEnd_2933129 := by exact prefixLift 2933129
  have htrace : WordTrace (prefixWord ++ tailWord_2933129) baseStart_2933129 baseEnd_2933129 := by
    simpa [prefixWord, tailWord_2933129, baseEnd_2933129] using wordTrace_append hprefix tailTrace_2933129
  have hstable : (prefixWord ++ tailWord_2933129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933129).length < 2 ^ (prefixWord ++ tailWord_2933129).sum := by decide
  have hdescent : baseEnd_2933129 < baseStart_2933129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933150 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2933150 : Nat := 118140960795 + 2933150 * 2 ^ 59
def prefixEnd_2933150 : Nat := 4983230072969 + 3 ^ 40 * 2933150 * 2
def baseEnd_2933150 : Nat := 502038593911768090278565

theorem tailTrace_2933150 : CollatzResearch.WordTrace tailWord_2933150 prefixEnd_2933150 502038593911768090278565 := by
  unfold tailWord_2933150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372596165463245872883613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71320512882470644655379269 13372596165463245872883613)
  ·
    refine ⟨5014723562048717202331355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13372596165463245872883613 5014723562048717202331355)
    ·
      refine ⟨7522085343073075803497033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014723562048717202331355 7522085343073075803497033)
      ·
        refine ⟨5641564007304806852622775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7522085343073075803497033 5641564007304806852622775)
        ·
          refine ⟨8462346010957210278934163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641564007304806852622775 8462346010957210278934163)
          ·
            refine ⟨12693519016435815418401245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462346010957210278934163 12693519016435815418401245)
            ·
              refine ⟨4760069631163430781900467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12693519016435815418401245 4760069631163430781900467)
              ·
                refine ⟨7140104446745146172850701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760069631163430781900467 7140104446745146172850701)
                ·
                  refine ⟨2677539167529429814819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7140104446745146172850701 2677539167529429814819013)
                  ·
                    refine ⟨502038593911768090278565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677539167529429814819013 502038593911768090278565)
                    ·
                      rfl

theorem cell23_2933150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2933150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933150 prefixEnd_2933150 := by exact prefixLift 2933150
  have htrace : WordTrace (prefixWord ++ tailWord_2933150) baseStart_2933150 baseEnd_2933150 := by
    simpa [prefixWord, tailWord_2933150, baseEnd_2933150] using wordTrace_append hprefix tailTrace_2933150
  have hstable : (prefixWord ++ tailWord_2933150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933150).length < 2 ^ (prefixWord ++ tailWord_2933150).sum := by decide
  have hdescent : baseEnd_2933150 < baseStart_2933150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933216 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2933216 : Nat := 118140960795 + 2933216 * 2 ^ 59
def prefixEnd_2933216 : Nat := 4983230072969 + 3 ^ 40 * 2933216 * 2
def baseEnd_2933216 : Nat := 1506149671458501012610391

theorem tailTrace_2933216 : CollatzResearch.WordTrace tailWord_2933216 prefixEnd_2933216 1506149671458501012610391 := by
  unfold tailWord_2933216
  simp only [CollatzResearch.WordTrace]
  refine ⟨53491588270733430127485751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71322117694311240169981001 53491588270733430127485751)
  ·
    refine ⟨80237382406100145191228627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53491588270733430127485751 80237382406100145191228627)
    ·
      refine ⟨120356073609150217786842941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80237382406100145191228627 120356073609150217786842941)
      ·
        refine ⟨45133527603431331670066103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120356073609150217786842941 45133527603431331670066103)
        ·
          refine ⟨67700291405146997505099155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45133527603431331670066103 67700291405146997505099155)
          ·
            refine ⟨101550437107720496257648733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67700291405146997505099155 101550437107720496257648733)
            ·
              refine ⟨38081413915395186096618275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101550437107720496257648733 38081413915395186096618275)
              ·
                refine ⟨57122120873092779144927413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38081413915395186096618275 57122120873092779144927413)
                ·
                  refine ⟨5355198831852448044836945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57122120873092779144927413 5355198831852448044836945)
                  ·
                    refine ⟨4016399123889336033627709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355198831852448044836945 4016399123889336033627709)
                    ·
                      refine ⟨1506149671458501012610391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016399123889336033627709 1506149671458501012610391)
                      ·
                        rfl

theorem cell23_2933216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2933216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933216 prefixEnd_2933216 := by exact prefixLift 2933216
  have htrace : WordTrace (prefixWord ++ tailWord_2933216) baseStart_2933216 baseEnd_2933216 := by
    simpa [prefixWord, tailWord_2933216, baseEnd_2933216] using wordTrace_append hprefix tailTrace_2933216
  have hstable : (prefixWord ++ tailWord_2933216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933216).length < 2 ^ (prefixWord ++ tailWord_2933216).sum := by decide
  have hdescent : baseEnd_2933216 < baseStart_2933216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933223 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 2, 4]
def baseStart_2933223 : Nat := 118140960795 + 2933223 * 2 ^ 59
def prefixEnd_2933223 : Nat := 4983230072969 + 3 ^ 40 * 2933223 * 2
def baseEnd_2933223 : Nat := 502051088607694161740953

theorem tailTrace_2933223 : CollatzResearch.WordTrace tailWord_2933223 prefixEnd_2933223 502051088607694161740953 := by
  unfold tailWord_2933223
  simp only [CollatzResearch.WordTrace]
  refine ⟨106983431852441500450476323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71322287901627666966984215 106983431852441500450476323)
  ·
    refine ⟨160475147778662250675714485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106983431852441500450476323 160475147778662250675714485)
    ·
      refine ⟨15044545104249586000848233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160475147778662250675714485 15044545104249586000848233)
      ·
        refine ⟨11283408828187189500636175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15044545104249586000848233 11283408828187189500636175)
        ·
          refine ⟨16925113242280784250954263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11283408828187189500636175 16925113242280784250954263)
          ·
            refine ⟨25387669863421176376431395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16925113242280784250954263 25387669863421176376431395)
            ·
              refine ⟨38081504795131764564647093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25387669863421176376431395 38081504795131764564647093)
              ·
                refine ⟨3570141074543602927935665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38081504795131764564647093 3570141074543602927935665)
                ·
                  refine ⟨2677605805907702195951749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3570141074543602927935665 2677605805907702195951749)
                  ·
                    refine ⟨502051088607694161740953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677605805907702195951749 502051088607694161740953)
                    ·
                      rfl

theorem cell23_2933223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_2933223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933223 prefixEnd_2933223 := by exact prefixLift 2933223
  have htrace : WordTrace (prefixWord ++ tailWord_2933223) baseStart_2933223 baseEnd_2933223 := by
    simpa [prefixWord, tailWord_2933223, baseEnd_2933223] using wordTrace_append hprefix tailTrace_2933223
  have hstable : (prefixWord ++ tailWord_2933223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933223).length < 2 ^ (prefixWord ++ tailWord_2933223).sum := by decide
  have hdescent : baseEnd_2933223 < baseStart_2933223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933230 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_2933230 : Nat := 118140960795 + 2933230 * 2 ^ 59
def prefixEnd_2933230 : Nat := 4983230072969 + 3 ^ 40 * 2933230 * 2
def baseEnd_2933230 : Nat := 1506156860187663957835327

theorem tailTrace_2933230 : CollatzResearch.WordTrace tailWord_2933230 prefixEnd_2933230 1506156860187663957835327 := by
  unfold tailWord_2933230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372960895427017580747643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71322458108944093763987429 13372960895427017580747643)
  ·
    refine ⟨20059441343140526371121465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13372960895427017580747643 20059441343140526371121465)
    ·
      refine ⟨15044581007355394778341099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20059441343140526371121465 15044581007355394778341099)
      ·
        refine ⟨22566871511033092167511649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044581007355394778341099 22566871511033092167511649)
        ·
          refine ⟨16925153633274819125633737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22566871511033092167511649 16925153633274819125633737)
          ·
            refine ⟨12693865224956114344225303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16925153633274819125633737 12693865224956114344225303)
            ·
              refine ⟨19040797837434171516337955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12693865224956114344225303 19040797837434171516337955)
              ·
                refine ⟨28561196756151257274506933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19040797837434171516337955 28561196756151257274506933)
                ·
                  refine ⟨2677612195889180369485025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28561196756151257274506933 2677612195889180369485025)
                  ·
                    refine ⟨2008209146916885277113769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677612195889180369485025 2008209146916885277113769)
                    ·
                      refine ⟨1506156860187663957835327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008209146916885277113769 1506156860187663957835327)
                      ·
                        rfl

theorem cell23_2933230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_2933230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933230 prefixEnd_2933230 := by exact prefixLift 2933230
  have htrace : WordTrace (prefixWord ++ tailWord_2933230) baseStart_2933230 baseEnd_2933230 := by
    simpa [prefixWord, tailWord_2933230, baseEnd_2933230] using wordTrace_append hprefix tailTrace_2933230
  have hstable : (prefixWord ++ tailWord_2933230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933230).length < 2 ^ (prefixWord ++ tailWord_2933230).sum := by decide
  have hdescent : baseEnd_2933230 < baseStart_2933230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933233 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_2933233 : Nat := 118140960795 + 2933233 * 2 ^ 59
def prefixEnd_2933233 : Nat := 4983230072969 + 3 ^ 40 * 2933233 * 2
def baseEnd_2933233 : Nat := 1506158400629627446097813

theorem tailTrace_2933233 : CollatzResearch.WordTrace tailWord_2933233 prefixEnd_2933233 1506158400629627446097813 := by
  unfold tailWord_2933233
  simp only [CollatzResearch.WordTrace]
  refine ⟨106983796582405272158340353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71322531054936848105560235 106983796582405272158340353)
  ·
    refine ⟨80237847436803954118755265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106983796582405272158340353 80237847436803954118755265)
    ·
      refine ⟨60178385577602965589066449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80237847436803954118755265 60178385577602965589066449)
      ·
        refine ⟨45133789183202224191799837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60178385577602965589066449 45133789183202224191799837)
        ·
          refine ⟨16925170943700834071924939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45133789183202224191799837 16925170943700834071924939)
          ·
            refine ⟨25387756415551251107887409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16925170943700834071924939 25387756415551251107887409)
            ·
              refine ⟨19040817311663438330915557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25387756415551251107887409 19040817311663438330915557)
              ·
                refine ⟨3570153245936894687046667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19040817311663438330915557 3570153245936894687046667)
                ·
                  refine ⟨5355229868905342030570001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570153245936894687046667 5355229868905342030570001)
                  ·
                    refine ⟨4016422401679006522927501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355229868905342030570001 4016422401679006522927501)
                    ·
                      refine ⟨1506158400629627446097813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016422401679006522927501 1506158400629627446097813)
                      ·
                        rfl

theorem cell23_2933233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_2933233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933233 prefixEnd_2933233 := by exact prefixLift 2933233
  have htrace : WordTrace (prefixWord ++ tailWord_2933233) baseStart_2933233 baseEnd_2933233 := by
    simpa [prefixWord, tailWord_2933233, baseEnd_2933233] using wordTrace_append hprefix tailTrace_2933233
  have hstable : (prefixWord ++ tailWord_2933233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933233).length < 2 ^ (prefixWord ++ tailWord_2933233).sum := by decide
  have hdescent : baseEnd_2933233 < baseStart_2933233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933234 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2933234 : Nat := 118140960795 + 2933234 * 2 ^ 59
def prefixEnd_2933234 : Nat := 4983230072969 + 3 ^ 40 * 2933234 * 2
def baseEnd_2933234 : Nat := 1506158914110281942185309

theorem tailTrace_2933234 : CollatzResearch.WordTrace tailWord_2933234 prefixEnd_2933234 1506158914110281942185309 := by
  unfold tailWord_2933234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26745958263850412332281689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71322555370267766219417837 26745958263850412332281689)
  ·
    refine ⟨20059468697887809249211267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26745958263850412332281689 20059468697887809249211267)
    ·
      refine ⟨30089203046831713873816901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20059468697887809249211267 30089203046831713873816901)
      ·
        refine ⟨5641725571280946351340669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30089203046831713873816901 5641725571280946351340669)
        ·
          refine ⟨2115647089230354881752751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5641725571280946351340669 2115647089230354881752751)
          ·
            refine ⟨3173470633845532322629127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115647089230354881752751 3173470633845532322629127)
            ·
              refine ⟨4760205950768298483943691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173470633845532322629127 4760205950768298483943691)
              ·
                refine ⟨7140308926152447725915537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760205950768298483943691 7140308926152447725915537)
                ·
                  refine ⟨5355231694614335794436653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7140308926152447725915537 5355231694614335794436653)
                  ·
                    refine ⟨2008211885480375922913745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5355231694614335794436653 2008211885480375922913745)
                    ·
                      refine ⟨1506158914110281942185309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008211885480375922913745 1506158914110281942185309)
                      ·
                        rfl

theorem cell23_2933234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2933234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933234 prefixEnd_2933234 := by exact prefixLift 2933234
  have htrace : WordTrace (prefixWord ++ tailWord_2933234) baseStart_2933234 baseEnd_2933234 := by
    simpa [prefixWord, tailWord_2933234, baseEnd_2933234] using wordTrace_append hprefix tailTrace_2933234
  have hstable : (prefixWord ++ tailWord_2933234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933234).length < 2 ^ (prefixWord ++ tailWord_2933234).sum := by decide
  have hdescent : baseEnd_2933234 < baseStart_2933234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933239 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2933239 : Nat := 118140960795 + 2933239 * 2 ^ 59
def prefixEnd_2933239 : Nat := 4983230072969 + 3 ^ 40 * 2933239 * 2
def baseEnd_2933239 : Nat := 1506161481513554422622785

theorem tailTrace_2933239 : CollatzResearch.WordTrace tailWord_2933239 prefixEnd_2933239 1506161481513554422622785 := by
  unfold tailWord_2933239
  simp only [CollatzResearch.WordTrace]
  refine ⟨106984015420383535183058771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71322676946922356788705847 106984015420383535183058771)
  ·
    refine ⟨160476023130575302774588157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106984015420383535183058771 160476023130575302774588157)
    ·
      refine ⟨60178508673965738540470559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160476023130575302774588157 60178508673965738540470559)
      ·
        refine ⟨90267763010948607810705839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60178508673965738540470559 90267763010948607810705839)
        ·
          refine ⟨135401644516422911716058759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90267763010948607810705839 135401644516422911716058759)
          ·
            refine ⟨203102466774634367574088139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135401644516422911716058759 203102466774634367574088139)
            ·
              refine ⟨304653700161951551361132209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203102466774634367574088139 304653700161951551361132209)
              ·
                refine ⟨228490275121463663520849157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304653700161951551361132209 228490275121463663520849157)
                ·
                  refine ⟨42841926585274436910159217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228490275121463663520849157 42841926585274436910159217)
                  ·
                    refine ⟨32131444938955827682619413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42841926585274436910159217 32131444938955827682619413)
                    ·
                      refine ⟨1506161481513554422622785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32131444938955827682619413 1506161481513554422622785)
                      ·
                        rfl

theorem cell23_2933239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2933239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933239 prefixEnd_2933239 := by exact prefixLift 2933239
  have htrace : WordTrace (prefixWord ++ tailWord_2933239) baseStart_2933239 baseEnd_2933239 := by
    simpa [prefixWord, tailWord_2933239, baseEnd_2933239] using wordTrace_append hprefix tailTrace_2933239
  have hstable : (prefixWord ++ tailWord_2933239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933239).length < 2 ^ (prefixWord ++ tailWord_2933239).sum := by decide
  have hdescent : baseEnd_2933239 < baseStart_2933239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933247 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 1, 2, 2]
def baseStart_2933247 : Nat := 118140960795 + 2933247 * 2 ^ 59
def prefixEnd_2933247 : Nat := 4983230072969 + 3 ^ 40 * 2933247 * 2
def baseEnd_2933247 : Nat := 1506165589358790391322749

theorem tailTrace_2933247 : CollatzResearch.WordTrace tailWord_2933247 prefixEnd_2933247 1506165589358790391322749 := by
  unfold tailWord_2933247
  simp only [CollatzResearch.WordTrace]
  refine ⟨106984307204354552549349995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71322871469569701699566663 106984307204354552549349995)
  ·
    refine ⟨160476460806531828824024993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106984307204354552549349995 160476460806531828824024993)
    ·
      refine ⟨120357345604898871618018745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160476460806531828824024993 120357345604898871618018745)
      ·
        refine ⟨90268009203674153713514059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120357345604898871618018745 90268009203674153713514059)
        ·
          refine ⟨135402013805511230570271089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90268009203674153713514059 135402013805511230570271089)
          ·
            refine ⟨101551510354133422927703317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135402013805511230570271089 101551510354133422927703317)
            ·
              refine ⟨4760227047850004199736093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101551510354133422927703317 4760227047850004199736093)
              ·
                refine ⟨1785085142943751574901035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4760227047850004199736093 1785085142943751574901035)
                ·
                  refine ⟨2677627714415627362351553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785085142943751574901035 2677627714415627362351553)
                  ·
                    refine ⟨2008220785811720521763665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677627714415627362351553 2008220785811720521763665)
                    ·
                      refine ⟨1506165589358790391322749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008220785811720521763665 1506165589358790391322749)
                      ·
                        rfl

theorem cell23_2933247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_2933247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933247 prefixEnd_2933247 := by exact prefixLift 2933247
  have htrace : WordTrace (prefixWord ++ tailWord_2933247) baseStart_2933247 baseEnd_2933247 := by
    simpa [prefixWord, tailWord_2933247, baseEnd_2933247] using wordTrace_append hprefix tailTrace_2933247
  have hstable : (prefixWord ++ tailWord_2933247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933247).length < 2 ^ (prefixWord ++ tailWord_2933247).sum := by decide
  have hdescent : baseEnd_2933247 < baseStart_2933247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933287 : List Nat := [1, 1, 7, 2, 1, 2, 2, 7]
def baseStart_2933287 : Nat := 118140960795 + 2933287 * 2 ^ 59
def prefixEnd_2933287 : Nat := 4983230072969 + 3 ^ 40 * 2933287 * 2
def baseEnd_2933287 : Nat := 55784671429072971660095

theorem tailTrace_2933287 : CollatzResearch.WordTrace tailWord_2933287 prefixEnd_2933287 55784671429072971660095 := by
  unfold tailWord_2933287
  simp only [CollatzResearch.WordTrace]
  refine ⟨106985766124209639380806115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71323844082806426253870743 106985766124209639380806115)
  ·
    refine ⟨160478649186314459071209173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106985766124209639380806115 160478649186314459071209173)
    ·
      refine ⟨3761218340304245134481465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160478649186314459071209173 3761218340304245134481465)
      ·
        refine ⟨2820913755228183850861099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761218340304245134481465 2820913755228183850861099)
        ·
          refine ⟨4231370632842275776291649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820913755228183850861099 4231370632842275776291649)
          ·
            refine ⟨3173527974631706832218737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4231370632842275776291649 3173527974631706832218737)
            ·
              refine ⟨2380145980973780124164053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173527974631706832218737 2380145980973780124164053)
              ·
                refine ⟨55784671429072971660095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2380145980973780124164053 55784671429072971660095)
                ·
                  rfl

theorem cell23_2933287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 7].length) (baseStart_2933287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933287 prefixEnd_2933287 := by exact prefixLift 2933287
  have htrace : WordTrace (prefixWord ++ tailWord_2933287) baseStart_2933287 baseEnd_2933287 := by
    simpa [prefixWord, tailWord_2933287, baseEnd_2933287] using wordTrace_append hprefix tailTrace_2933287
  have hstable : (prefixWord ++ tailWord_2933287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933287).length < 2 ^ (prefixWord ++ tailWord_2933287).sum := by decide
  have hdescent : baseEnd_2933287 < baseStart_2933287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933303 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_2933303 : Nat := 118140960795 + 2933303 * 2 ^ 59
def prefixEnd_2933303 : Nat := 4983230072969 + 3 ^ 40 * 2933303 * 2
def baseEnd_2933303 : Nat := 1506194344275442172222491

theorem tailTrace_2933303 : CollatzResearch.WordTrace tailWord_2933303 prefixEnd_2933303 1506194344275442172222491 := by
  unfold tailWord_2933303
  simp only [CollatzResearch.WordTrace]
  refine ⟨106986349692151674113388563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71324233128101116075592375 106986349692151674113388563)
  ·
    refine ⟨160479524538227511170082845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106986349692151674113388563 160479524538227511170082845)
    ·
      refine ⟨60179821701835316688781067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160479524538227511170082845 60179821701835316688781067)
      ·
        refine ⟨90269732552752975033171601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60179821701835316688781067 90269732552752975033171601)
        ·
          refine ⟨67702299414564731274878701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90269732552752975033171601 67702299414564731274878701)
          ·
            refine ⟨25388362280461774228079513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67702299414564731274878701 25388362280461774228079513)
            ·
              refine ⟨19041271710346330671059635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25388362280461774228079513 19041271710346330671059635)
              ·
                refine ⟨28561907565519496006589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19041271710346330671059635 28561907565519496006589453)
                ·
                  refine ⟨10710715337069811002471045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28561907565519496006589453 10710715337069811002471045)
                  ·
                    refine ⟨2008259125700589562963321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10710715337069811002471045 2008259125700589562963321)
                    ·
                      refine ⟨1506194344275442172222491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008259125700589562963321 1506194344275442172222491)
                      ·
                        rfl

theorem cell23_2933303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_2933303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933303 prefixEnd_2933303 := by exact prefixLift 2933303
  have htrace : WordTrace (prefixWord ++ tailWord_2933303) baseStart_2933303 baseEnd_2933303 := by
    simpa [prefixWord, tailWord_2933303, baseEnd_2933303] using wordTrace_append hprefix tailTrace_2933303
  have hstable : (prefixWord ++ tailWord_2933303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933303).length < 2 ^ (prefixWord ++ tailWord_2933303).sum := by decide
  have hdescent : baseEnd_2933303 < baseStart_2933303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933306 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2933306 : Nat := 118140960795 + 2933306 * 2 ^ 59
def prefixEnd_2933306 : Nat := 4983230072969 + 3 ^ 40 * 2933306 * 2
def baseEnd_2933306 : Nat := 1506195884717405660484977

theorem tailTrace_2933306 : CollatzResearch.WordTrace tailWord_2933306 prefixEnd_2933306 1506195884717405660484977 := by
  unfold tailWord_2933306
  simp only [CollatzResearch.WordTrace]
  refine ⟨26746614777785201406436943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71324306074093870417165181 26746614777785201406436943)
  ·
    refine ⟨40119922166677802109655415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26746614777785201406436943 40119922166677802109655415)
    ·
      refine ⟨60179883250016703164483123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40119922166677802109655415 60179883250016703164483123)
      ·
        refine ⟨90269824875025054746724685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60179883250016703164483123 90269824875025054746724685)
        ·
          refine ⟨33851184328134395530021757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90269824875025054746724685 33851184328134395530021757)
          ·
            refine ⟨12694194123050398323758159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33851184328134395530021757 12694194123050398323758159)
            ·
              refine ⟨19041291184575597485637239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694194123050398323758159 19041291184575597485637239)
              ·
                refine ⟨28561936776863396228455859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19041291184575597485637239 28561936776863396228455859)
                ·
                  refine ⟨42842905165295094342683789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28561936776863396228455859 42842905165295094342683789)
                  ·
                    refine ⟨16066089436985660378506421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42842905165295094342683789 16066089436985660378506421)
                    ·
                      refine ⟨1506195884717405660484977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16066089436985660378506421 1506195884717405660484977)
                      ·
                        rfl

theorem cell23_2933306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2933306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933306 prefixEnd_2933306 := by exact prefixLift 2933306
  have htrace : WordTrace (prefixWord ++ tailWord_2933306) baseStart_2933306 baseEnd_2933306 := by
    simpa [prefixWord, tailWord_2933306, baseEnd_2933306] using wordTrace_append hprefix tailTrace_2933306
  have hstable : (prefixWord ++ tailWord_2933306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933306).length < 2 ^ (prefixWord ++ tailWord_2933306).sum := by decide
  have hdescent : baseEnd_2933306 < baseStart_2933306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933356 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_2933356 : Nat := 118140960795 + 2933356 * 2 ^ 59
def prefixEnd_2933356 : Nat := 4983230072969 + 3 ^ 40 * 2933356 * 2
def baseEnd_2933356 : Nat := 502073852916710154953249

theorem tailTrace_2933356 : CollatzResearch.WordTrace tailWord_2933356 prefixEnd_2933356 502073852916710154953249 := by
  unfold tailWord_2933356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53494141380479832082533961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71325521840639776110045281 53494141380479832082533961)
  ·
    refine ⟨40120606035359874061900471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53494141380479832082533961 40120606035359874061900471)
    ·
      refine ⟨60180909053039811092850707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40120606035359874061900471 60180909053039811092850707)
      ·
        refine ⟨90271363579559716639276061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60180909053039811092850707 90271363579559716639276061)
        ·
          refine ⟨33851761342334893739728523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90271363579559716639276061 33851761342334893739728523)
          ·
            refine ⟨50777642013502340609592785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33851761342334893739728523 50777642013502340609592785)
            ·
              refine ⟨38083231510126755457194589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50777642013502340609592785 38083231510126755457194589)
              ·
                refine ⟨14281211816297533296447971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38083231510126755457194589 14281211816297533296447971)
                ·
                  refine ⟨21421817724446299944671957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14281211816297533296447971 21421817724446299944671957)
                  ·
                    refine ⟨502073852916710154953249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21421817724446299944671957 502073852916710154953249)
                    ·
                      rfl

theorem cell23_2933356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_2933356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933356 prefixEnd_2933356 := by exact prefixLift 2933356
  have htrace : WordTrace (prefixWord ++ tailWord_2933356) baseStart_2933356 baseEnd_2933356 := by
    simpa [prefixWord, tailWord_2933356, baseEnd_2933356] using wordTrace_append hprefix tailTrace_2933356
  have hstable : (prefixWord ++ tailWord_2933356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933356).length < 2 ^ (prefixWord ++ tailWord_2933356).sum := by decide
  have hdescent : baseEnd_2933356 < baseStart_2933356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933380 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2933380 : Nat := 118140960795 + 2933380 * 2 ^ 59
def prefixEnd_2933380 : Nat := 4983230072969 + 3 ^ 40 * 2933380 * 2
def baseEnd_2933380 : Nat := 1506233882285838370959637

theorem tailTrace_2933380 : CollatzResearch.WordTrace tailWord_2933380 prefixEnd_2933380 1506233882285838370959637 := by
  unfold tailWord_2933380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53494579056436358131970797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71326105408581810842627729 53494579056436358131970797)
  ·
    refine ⟨20060467146163634299489049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53494579056436358131970797 20060467146163634299489049)
    ·
      refine ⟨15045350359622725724616787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20060467146163634299489049 15045350359622725724616787)
      ·
        refine ⟨22568025539434088586925181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15045350359622725724616787 22568025539434088586925181)
        ·
          refine ⟨8463009577287783220096943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22568025539434088586925181 8463009577287783220096943)
          ·
            refine ⟨12694514365931674830145415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463009577287783220096943 12694514365931674830145415)
            ·
              refine ⟨19041771548897512245218123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694514365931674830145415 19041771548897512245218123)
              ·
                refine ⟨28562657323346268367827185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19041771548897512245218123 28562657323346268367827185)
                ·
                  refine ⟨21421992992509701275870389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28562657323346268367827185 21421992992509701275870389)
                  ·
                    refine ⟨2008311843047784494612849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21421992992509701275870389 2008311843047784494612849)
                    ·
                      refine ⟨1506233882285838370959637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008311843047784494612849 1506233882285838370959637)
                      ·
                        rfl

theorem cell23_2933380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2933380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933380 prefixEnd_2933380 := by exact prefixLift 2933380
  have htrace : WordTrace (prefixWord ++ tailWord_2933380) baseStart_2933380 baseEnd_2933380 := by
    simpa [prefixWord, tailWord_2933380, baseEnd_2933380] using wordTrace_append hprefix tailTrace_2933380
  have hstable : (prefixWord ++ tailWord_2933380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933380).length < 2 ^ (prefixWord ++ tailWord_2933380).sum := by decide
  have hdescent : baseEnd_2933380 < baseStart_2933380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933437 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2933437 : Nat := 118140960795 + 2933437 * 2 ^ 59
def prefixEnd_2933437 : Nat := 4983230072969 + 3 ^ 40 * 2933437 * 2
def baseEnd_2933437 : Nat := 502087716894381549315625

theorem tailTrace_2933437 : CollatzResearch.WordTrace tailWord_2933437 prefixEnd_2933437 502087716894381549315625 := by
  unfold tailWord_2933437
  simp only [CollatzResearch.WordTrace]
  refine ⟨106991237073666214998766565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71327491382444143332511043 106991237073666214998766565)
  ·
    refine ⟨20060856951312415312268731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106991237073666214998766565 20060856951312415312268731)
    ·
      refine ⟨30091285426968622968403097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20060856951312415312268731 30091285426968622968403097)
      ·
        refine ⟨22568464070226467226302323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30091285426968622968403097 22568464070226467226302323)
        ·
          refine ⟨33852696105339700839453485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22568464070226467226302323 33852696105339700839453485)
          ·
            refine ⟨12694761039502387814795057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33852696105339700839453485 12694761039502387814795057)
            ·
              refine ⟨9521070779626790861096293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694761039502387814795057 9521070779626790861096293)
              ·
                refine ⟨1785200771180023286455555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9521070779626790861096293 1785200771180023286455555)
                ·
                  refine ⟨2677801156770034929683333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785200771180023286455555 2677801156770034929683333)
                  ·
                    refine ⟨502087716894381549315625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2677801156770034929683333 502087716894381549315625)
                    ·
                      rfl

theorem cell23_2933437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2933437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933437 prefixEnd_2933437 := by exact prefixLift 2933437
  have htrace : WordTrace (prefixWord ++ tailWord_2933437) baseStart_2933437 baseEnd_2933437 := by
    simpa [prefixWord, tailWord_2933437, baseEnd_2933437] using wordTrace_append hprefix tailTrace_2933437
  have hstable : (prefixWord ++ tailWord_2933437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933437).length < 2 ^ (prefixWord ++ tailWord_2933437).sum := by decide
  have hdescent : baseEnd_2933437 < baseStart_2933437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933483 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4]
def baseStart_2933483 : Nat := 118140960795 + 2933483 * 2 ^ 59
def prefixEnd_2933483 : Nat := 4983230072969 + 3 ^ 40 * 2933483 * 2
def baseEnd_2933483 : Nat := 1506286770793251467971663

theorem tailTrace_2933483 : CollatzResearch.WordTrace tailWord_2933483 prefixEnd_2933483 1506286770793251467971663 := by
  unfold tailWord_2933483
  simp only [CollatzResearch.WordTrace]
  refine ⟨106992914831499564854941103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71328609887666376569960735 106992914831499564854941103)
  ·
    refine ⟨160489372247249347282411655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106992914831499564854941103 160489372247249347282411655)
    ·
      refine ⟨240734058370874020923617483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160489372247249347282411655 240734058370874020923617483)
      ·
        refine ⟨361101087556311031385426225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240734058370874020923617483 361101087556311031385426225)
        ·
          refine ⟨270825815667233273539069669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361101087556311031385426225 270825815667233273539069669)
          ·
            refine ⟨50779840437606238788575563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270825815667233273539069669 50779840437606238788575563)
            ·
              refine ⟨76169760656409358182863345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50779840437606238788575563 76169760656409358182863345)
              ·
                refine ⟨57127320492307018637147509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76169760656409358182863345 57127320492307018637147509)
                ·
                  refine ⟨5355686296153782997232579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57127320492307018637147509 5355686296153782997232579)
                  ·
                    refine ⟨8033529444230674495848869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5355686296153782997232579 8033529444230674495848869)
                    ·
                      refine ⟨1506286770793251467971663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8033529444230674495848869 1506286770793251467971663)
                      ·
                        rfl

theorem cell23_2933483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_2933483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933483 prefixEnd_2933483 := by exact prefixLift 2933483
  have htrace : WordTrace (prefixWord ++ tailWord_2933483) baseStart_2933483 baseEnd_2933483 := by
    simpa [prefixWord, tailWord_2933483, baseEnd_2933483] using wordTrace_append hprefix tailTrace_2933483
  have hstable : (prefixWord ++ tailWord_2933483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933483).length < 2 ^ (prefixWord ++ tailWord_2933483).sum := by decide
  have hdescent : baseEnd_2933483 < baseStart_2933483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933487 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 2, 3, 2]
def baseStart_2933487 : Nat := 118140960795 + 2933487 * 2 ^ 59
def prefixEnd_2933487 : Nat := 4983230072969 + 3 ^ 40 * 2933487 * 2
def baseEnd_2933487 : Nat := 1506288824715869452321645

theorem tailTrace_2933487 : CollatzResearch.WordTrace tailWord_2933487 prefixEnd_2933487 1506288824715869452321645 := by
  unfold tailWord_2933487
  simp only [CollatzResearch.WordTrace]
  refine ⟨106993060723485073538086715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71328707148990049025391143 106993060723485073538086715)
  ·
    refine ⟨160489591085227610307130073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106993060723485073538086715 160489591085227610307130073)
    ·
      refine ⟨120367193313920707730347555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160489591085227610307130073 120367193313920707730347555)
      ·
        refine ⟨180550789970881061595521333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120367193313920707730347555 180550789970881061595521333)
        ·
          refine ⟨16926636559770099524580125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180550789970881061595521333 16926636559770099524580125)
          ·
            refine ⟨6347488709913787321717547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16926636559770099524580125 6347488709913787321717547)
            ·
              refine ⟨9521233064870680982576321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347488709913787321717547 9521233064870680982576321)
              ·
                refine ⟨7140924798653010736932241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521233064870680982576321 7140924798653010736932241)
                ·
                  refine ⟨5355693598989758052699181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7140924798653010736932241 5355693598989758052699181)
                  ·
                    refine ⟨2008385099621159269762193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5355693598989758052699181 2008385099621159269762193)
                    ·
                      refine ⟨1506288824715869452321645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008385099621159269762193 1506288824715869452321645)
                      ·
                        rfl

theorem cell23_2933487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3, 2].length) (baseStart_2933487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933487 prefixEnd_2933487 := by exact prefixLift 2933487
  have htrace : WordTrace (prefixWord ++ tailWord_2933487) baseStart_2933487 baseEnd_2933487 := by
    simpa [prefixWord, tailWord_2933487, baseEnd_2933487] using wordTrace_append hprefix tailTrace_2933487
  have hstable : (prefixWord ++ tailWord_2933487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933487).length < 2 ^ (prefixWord ++ tailWord_2933487).sum := by decide
  have hdescent : baseEnd_2933487 < baseStart_2933487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933503 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_2933503 : Nat := 118140960795 + 2933503 * 2 ^ 59
def prefixEnd_2933503 : Nat := 4983230072969 + 3 ^ 40 * 2933503 * 2
def baseEnd_2933503 : Nat := 1506297040406341389721571

theorem tailTrace_2933503 : CollatzResearch.WordTrace tailWord_2933503 prefixEnd_2933503 1506297040406341389721571 := by
  unfold tailWord_2933503
  simp only [CollatzResearch.WordTrace]
  refine ⟨106993644291427108270669163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71329096194284738847112775 106993644291427108270669163)
  ·
    refine ⟨160490466437140662406003745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106993644291427108270669163 160490466437140662406003745)
    ·
      refine ⟨120367849827855496804502809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160490466437140662406003745 120367849827855496804502809)
      ·
        refine ⟨90275887370891622603377107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120367849827855496804502809 90275887370891622603377107)
        ·
          refine ⟨135413831056337433905065661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90275887370891622603377107 135413831056337433905065661)
          ·
            refine ⟨50780186646126537714399623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135413831056337433905065661 50780186646126537714399623)
            ·
              refine ⟨76170279969189806571599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50780186646126537714399623 76170279969189806571599435)
              ·
                refine ⟨114255419953784709857399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76170279969189806571599435 114255419953784709857399153)
                ·
                  refine ⟨85691564965338532393049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114255419953784709857399153 85691564965338532393049365)
                  ·
                    refine ⟨4016792107750243705924189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85691564965338532393049365 4016792107750243705924189)
                    ·
                      refine ⟨1506297040406341389721571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016792107750243705924189 1506297040406341389721571)
                      ·
                        rfl

theorem cell23_2933503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_2933503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933503 prefixEnd_2933503 := by exact prefixLift 2933503
  have htrace : WordTrace (prefixWord ++ tailWord_2933503) baseStart_2933503 baseEnd_2933503 := by
    simpa [prefixWord, tailWord_2933503, baseEnd_2933503] using wordTrace_append hprefix tailTrace_2933503
  have hstable : (prefixWord ++ tailWord_2933503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933503).length < 2 ^ (prefixWord ++ tailWord_2933503).sum := by decide
  have hdescent : baseEnd_2933503 < baseStart_2933503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933513 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2933513 : Nat := 118140960795 + 2933513 * 2 ^ 59
def prefixEnd_2933513 : Nat := 4983230072969 + 3 ^ 40 * 2933513 * 2
def baseEnd_2933513 : Nat := 1506302175212886350596525

theorem tailTrace_2933513 : CollatzResearch.WordTrace tailWord_2933513 prefixEnd_2933513 1506302175212886350596525 := by
  unfold tailWord_2933513
  simp only [CollatzResearch.WordTrace]
  refine ⟨106994009021390879978533193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71329339347593919985688795 106994009021390879978533193)
  ·
    refine ⟨80245506766043159983899895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106994009021390879978533193 80245506766043159983899895)
    ·
      refine ⟨120368260149064739975849843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80245506766043159983899895 120368260149064739975849843)
      ·
        refine ⟨180552390223597109963774765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120368260149064739975849843 180552390223597109963774765)
        ·
          refine ⟨67707146333848916236415537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180552390223597109963774765 67707146333848916236415537)
          ·
            refine ⟨50780359750386687177311653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67707146333848916236415537 50780359750386687177311653)
            ·
              refine ⟨9521317453197503845745935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50780359750386687177311653 9521317453197503845745935)
              ·
                refine ⟨14281976179796255768618903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521317453197503845745935 14281976179796255768618903)
                ·
                  refine ⟨21422964269694383652928355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14281976179796255768618903 21422964269694383652928355)
                  ·
                    refine ⟨32134446404541575479392533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21422964269694383652928355 32134446404541575479392533)
                    ·
                      refine ⟨1506302175212886350596525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32134446404541575479392533 1506302175212886350596525)
                      ·
                        rfl

theorem cell23_2933513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2933513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933513 prefixEnd_2933513 := by exact prefixLift 2933513
  have htrace : WordTrace (prefixWord ++ tailWord_2933513) baseStart_2933513 baseEnd_2933513 := by
    simpa [prefixWord, tailWord_2933513, baseEnd_2933513] using wordTrace_append hprefix tailTrace_2933513
  have hstable : (prefixWord ++ tailWord_2933513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933513).length < 2 ^ (prefixWord ++ tailWord_2933513).sum := by decide
  have hdescent : baseEnd_2933513 < baseStart_2933513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
