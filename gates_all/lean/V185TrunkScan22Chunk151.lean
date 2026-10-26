import V185TrunkScan22Chunk150

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1349565 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1349565 : Nat := 118140960795 + 1349565 * 2 ^ 59
def prefixEnd_1349565 : Nat := 4983230072969 + 3 ^ 40 * 1349565 * 2
def baseEnd_1349565 : Nat := 461983679656745036287313

theorem tailTrace_1349565 : CollatzResearch.WordTrace tailWord_1349565 prefixEnd_1349565 461983679656745036287313 := by
  unfold tailWord_1349565
  simp only [CollatzResearch.WordTrace]
  refine ⟨49222679355763967197074149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32815119570509311464716099 49222679355763967197074149)
  ·
    refine ⟨9229252379205743849451403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49222679355763967197074149 9229252379205743849451403)
    ·
      refine ⟨13843878568808615774177105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9229252379205743849451403 13843878568808615774177105)
      ·
        refine ⟨10382908926606461830632829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13843878568808615774177105 10382908926606461830632829)
        ·
          refine ⟨3893590847477423186487311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10382908926606461830632829 3893590847477423186487311)
          ·
            refine ⟨5840386271216134779730967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893590847477423186487311 5840386271216134779730967)
            ·
              refine ⟨8760579406824202169596451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840386271216134779730967 8760579406824202169596451)
              ·
                refine ⟨13140869110236303254394677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760579406824202169596451 13140869110236303254394677)
                ·
                  refine ⟨1231956479084653430099501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13140869110236303254394677 1231956479084653430099501)
                  ·
                    refine ⟨461983679656745036287313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231956479084653430099501 461983679656745036287313)
                    ·
                      rfl

theorem cell22_1349565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1349565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349565 prefixEnd_1349565 := by exact prefixLift 1349565
  have htrace : WordTrace (prefixWord ++ tailWord_1349565) baseStart_1349565 baseEnd_1349565 := by
    simpa [prefixWord, tailWord_1349565, baseEnd_1349565] using wordTrace_append hprefix tailTrace_1349565
  have hstable : (prefixWord ++ tailWord_1349565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349565).length < 2 ^ (prefixWord ++ tailWord_1349565).sum := by decide
  have hdescent : baseEnd_1349565 < baseStart_1349565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349625 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_1349625 : Nat := 118140960795 + 1349625 * 2 ^ 59
def prefixEnd_1349625 : Nat := 4983230072969 + 3 ^ 40 * 1349625 * 2
def baseEnd_1349625 : Nat := 462004218882924879787129

theorem tailTrace_1349625 : CollatzResearch.WordTrace tailWord_1349625 prefixEnd_1349625 462004218882924879787129 := by
  unfold tailWord_1349625
  simp only [CollatzResearch.WordTrace]
  refine ⟨49224867735546597444258329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32816578490364398296172219 49224867735546597444258329)
  ·
    refine ⟨36918650801659948083193747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49224867735546597444258329 36918650801659948083193747)
    ·
      refine ⟨55377976202489922124790621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36918650801659948083193747 55377976202489922124790621)
      ·
        refine ⟨20766741075933720796796483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55377976202489922124790621 20766741075933720796796483)
        ·
          refine ⟨31150111613900581195194725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20766741075933720796796483 31150111613900581195194725)
          ·
            refine ⟨5840645927606358974099011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31150111613900581195194725 5840645927606358974099011)
            ·
              refine ⟨8760968891409538461148517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840645927606358974099011 8760968891409538461148517)
              ·
                refine ⟨1642681667139288461465347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8760968891409538461148517 1642681667139288461465347)
                ·
                  refine ⟨2464022500708932692198021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642681667139288461465347 2464022500708932692198021)
                  ·
                    refine ⟨462004218882924879787129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464022500708932692198021 462004218882924879787129)
                    ·
                      rfl

theorem cell22_1349625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_1349625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349625 prefixEnd_1349625 := by exact prefixLift 1349625
  have htrace : WordTrace (prefixWord ++ tailWord_1349625) baseStart_1349625 baseEnd_1349625 := by
    simpa [prefixWord, tailWord_1349625, baseEnd_1349625] using wordTrace_append hprefix tailTrace_1349625
  have hstable : (prefixWord ++ tailWord_1349625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349625).length < 2 ^ (prefixWord ++ tailWord_1349625).sum := by decide
  have hdescent : baseEnd_1349625 < baseStart_1349625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349683 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_1349683 : Nat := 118140960795 + 1349683 * 2 ^ 59
def prefixEnd_1349683 : Nat := 4983230072969 + 3 ^ 40 * 1349683 * 2
def baseEnd_1349683 : Nat := 462024073468232061836951

theorem tailTrace_1349683 : CollatzResearch.WordTrace tailWord_1349683 prefixEnd_1349683 462024073468232061836951 := by
  unfold tailWord_1349683
  simp only [CollatzResearch.WordTrace]
  refine ⟨49226983169336473349869703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32817988779557648899913135 49226983169336473349869703)
  ·
    refine ⟨73840474754004710024804555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49226983169336473349869703 73840474754004710024804555)
    ·
      refine ⟨110760712131007065037206833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73840474754004710024804555 110760712131007065037206833)
      ·
        refine ⟨83070534098255298777905125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110760712131007065037206833 83070534098255298777905125)
        ·
          refine ⟨15575725143422868520857211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83070534098255298777905125 15575725143422868520857211)
          ·
            refine ⟨23363587715134302781285817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15575725143422868520857211 23363587715134302781285817)
            ·
              refine ⟨17522690786350727085964363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23363587715134302781285817 17522690786350727085964363)
              ·
                refine ⟨26284036179526090628946545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17522690786350727085964363 26284036179526090628946545)
                ·
                  refine ⟨19713027134644567971709909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26284036179526090628946545 19713027134644567971709909)
                  ·
                    refine ⟨462024073468232061836951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19713027134644567971709909 462024073468232061836951)
                    ·
                      rfl

theorem cell22_1349683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_1349683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349683 prefixEnd_1349683 := by exact prefixLift 1349683
  have htrace : WordTrace (prefixWord ++ tailWord_1349683) baseStart_1349683 baseEnd_1349683 := by
    simpa [prefixWord, tailWord_1349683, baseEnd_1349683] using wordTrace_append hprefix tailTrace_1349683
  have hstable : (prefixWord ++ tailWord_1349683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349683).length < 2 ^ (prefixWord ++ tailWord_1349683).sum := by decide
  have hdescent : baseEnd_1349683 < baseStart_1349683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349794 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1349794 : Nat := 118140960795 + 1349794 * 2 ^ 59
def prefixEnd_1349794 : Nat := 4983230072969 + 3 ^ 40 * 1349794 * 2
def baseEnd_1349794 : Nat := 462062071036664772311611

theorem tailTrace_1349794 : CollatzResearch.WordTrace tailWord_1349794 prefixEnd_1349794 462062071036664772311611 := by
  unfold tailWord_1349794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307757917983584826790109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32820687781289559538106957 12307757917983584826790109)
  ·
    refine ⟨4615409219243844310046291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12307757917983584826790109 4615409219243844310046291)
    ·
      refine ⟨6923113828865766465069437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615409219243844310046291 6923113828865766465069437)
      ·
        refine ⟨2596167685824662424401039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6923113828865766465069437 2596167685824662424401039)
        ·
          refine ⟨3894251528736993636601559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596167685824662424401039 3894251528736993636601559)
          ·
            refine ⟨5841377293105490454902339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894251528736993636601559 5841377293105490454902339)
            ·
              refine ⟨8762065939658235682353509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841377293105490454902339 8762065939658235682353509)
              ·
                refine ⟨1642887363685919190441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8762065939658235682353509 1642887363685919190441283)
                ·
                  refine ⟨2464331045528878785661925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642887363685919190441283 2464331045528878785661925)
                  ·
                    refine ⟨462062071036664772311611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464331045528878785661925 462062071036664772311611)
                    ·
                      rfl

theorem cell22_1349794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1349794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349794 prefixEnd_1349794 := by exact prefixLift 1349794
  have htrace : WordTrace (prefixWord ++ tailWord_1349794) baseStart_1349794 baseEnd_1349794 := by
    simpa [prefixWord, tailWord_1349794, baseEnd_1349794] using wordTrace_append hprefix tailTrace_1349794
  have hstable : (prefixWord ++ tailWord_1349794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349794).length < 2 ^ (prefixWord ++ tailWord_1349794).sum := by decide
  have hdescent : baseEnd_1349794 < baseStart_1349794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349826 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1349826 : Nat := 118140960795 + 1349826 * 2 ^ 59
def prefixEnd_1349826 : Nat := 4983230072969 + 3 ^ 40 * 1349826 * 2
def baseEnd_1349826 : Nat := 154024341763542451837171

theorem tailTrace_1349826 : CollatzResearch.WordTrace tailWord_1349826 prefixEnd_1349826 154024341763542451837171 := by
  unfold tailWord_1349826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308049701954602193081333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32821465871878939181550221 12308049701954602193081333)
  ·
    refine ⟨1153879659558243955601375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12308049701954602193081333 1153879659558243955601375)
    ·
      refine ⟨1730819489337365933402063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153879659558243955601375 1730819489337365933402063)
      ·
        refine ⟨2596229234006048900103095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730819489337365933402063 2596229234006048900103095)
        ·
          refine ⟨3894343851009073350154643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596229234006048900103095 3894343851009073350154643)
          ·
            refine ⟨5841515776513610025231965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894343851009073350154643 5841515776513610025231965)
            ·
              refine ⟨2190568416192603759461987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5841515776513610025231965 2190568416192603759461987)
              ·
                refine ⟨3285852624288905639192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190568416192603759461987 3285852624288905639192981)
                ·
                  refine ⟨154024341763542451837171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3285852624288905639192981 154024341763542451837171)
                  ·
                    rfl

theorem cell22_1349826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1349826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349826 prefixEnd_1349826 := by exact prefixLift 1349826
  have htrace : WordTrace (prefixWord ++ tailWord_1349826) baseStart_1349826 baseEnd_1349826 := by
    simpa [prefixWord, tailWord_1349826, baseEnd_1349826] using wordTrace_append hprefix tailTrace_1349826
  have hstable : (prefixWord ++ tailWord_1349826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349826).length < 2 ^ (prefixWord ++ tailWord_1349826).sum := by decide
  have hdescent : baseEnd_1349826 < baseStart_1349826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349858 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1349858 : Nat := 118140960795 + 1349858 * 2 ^ 59
def prefixEnd_1349858 : Nat := 4983230072969 + 3 ^ 40 * 1349858 * 2
def baseEnd_1349858 : Nat := 462083979544589938711415

theorem tailTrace_1349858 : CollatzResearch.WordTrace tailWord_1349858 prefixEnd_1349858 462083979544589938711415 := by
  unfold tailWord_1349858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308341485925619559372557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32822243962468318824993485 12308341485925619559372557)
  ·
    refine ⟨4615628057222107334764709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12308341485925619559372557 4615628057222107334764709)
    ·
      refine ⟨865430260729145125268383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4615628057222107334764709 865430260729145125268383)
      ·
        refine ⟨1298145391093717687902575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865430260729145125268383 1298145391093717687902575)
        ·
          refine ⟨1947218086640576531853863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298145391093717687902575 1947218086640576531853863)
          ·
            refine ⟨2920827129960864797780795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947218086640576531853863 2920827129960864797780795)
            ·
              refine ⟨4381240694941297196671193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920827129960864797780795 4381240694941297196671193)
              ·
                refine ⟨3285930521205972897503395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381240694941297196671193 3285930521205972897503395)
                ·
                  refine ⟨4928895781808959346255093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285930521205972897503395 4928895781808959346255093)
                  ·
                    refine ⟨462083979544589938711415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4928895781808959346255093 462083979544589938711415)
                    ·
                      rfl

theorem cell22_1349858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1349858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349858 prefixEnd_1349858 := by exact prefixLift 1349858
  have htrace : WordTrace (prefixWord ++ tailWord_1349858) baseStart_1349858 baseEnd_1349858 := by
    simpa [prefixWord, tailWord_1349858, baseEnd_1349858] using wordTrace_append hprefix tailTrace_1349858
  have hstable : (prefixWord ++ tailWord_1349858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349858).length < 2 ^ (prefixWord ++ tailWord_1349858).sum := by decide
  have hdescent : baseEnd_1349858 < baseStart_1349858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349880 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1349880 : Nat := 118140960795 + 1349880 * 2 ^ 59
def prefixEnd_1349880 : Nat := 4983230072969 + 3 ^ 40 * 1349880 * 2
def baseEnd_1349880 : Nat := 462091510594189214661347

theorem tailTrace_1349880 : CollatzResearch.WordTrace tailWord_1349880 prefixEnd_1349880 462091510594189214661347 := by
  unfold tailWord_1349880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617084174811387997395547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32822778899748517329860729 24617084174811387997395547)
  ·
    refine ⟨36925626262217081996093321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24617084174811387997395547 36925626262217081996093321)
    ·
      refine ⟨27694219696662811497069991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36925626262217081996093321 27694219696662811497069991)
      ·
        refine ⟨41541329544994217245604987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27694219696662811497069991 41541329544994217245604987)
        ·
          refine ⟨62311994317491325868407481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41541329544994217245604987 62311994317491325868407481)
          ·
            refine ⟨46733995738118494401305611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62311994317491325868407481 46733995738118494401305611)
            ·
              refine ⟨70100993607177741601958417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46733995738118494401305611 70100993607177741601958417)
              ·
                refine ⟨52575745205383306201468813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70100993607177741601958417 52575745205383306201468813)
                ·
                  refine ⟨19715904452018739825550805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52575745205383306201468813 19715904452018739825550805)
                  ·
                    refine ⟨462091510594189214661347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19715904452018739825550805 462091510594189214661347)
                    ·
                      rfl

theorem cell22_1349880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1349880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349880 prefixEnd_1349880 := by exact prefixLift 1349880
  have htrace : WordTrace (prefixWord ++ tailWord_1349880) baseStart_1349880 baseEnd_1349880 := by
    simpa [prefixWord, tailWord_1349880, baseEnd_1349880] using wordTrace_append hprefix tailTrace_1349880
  have hstable : (prefixWord ++ tailWord_1349880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349880).length < 2 ^ (prefixWord ++ tailWord_1349880).sum := by decide
  have hdescent : baseEnd_1349880 < baseStart_1349880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349882 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_1349882 : Nat := 118140960795 + 1349882 * 2 ^ 59
def prefixEnd_1349882 : Nat := 4983230072969 + 3 ^ 40 * 1349882 * 2
def baseEnd_1349882 : Nat := 154030731745020625370447

theorem tailTrace_1349882 : CollatzResearch.WordTrace tailWord_1349882 prefixEnd_1349882 154030731745020625370447 := by
  unfold tailWord_1349882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308560323903882584090975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32822827530410353557575933 12308560323903882584090975)
  ·
    refine ⟨18462840485855823876136463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12308560323903882584090975 18462840485855823876136463)
    ·
      refine ⟨27694260728783735814204695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18462840485855823876136463 27694260728783735814204695)
      ·
        refine ⟨41541391093175603721307043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27694260728783735814204695 41541391093175603721307043)
        ·
          refine ⟨62312086639763405581960565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41541391093175603721307043 62312086639763405581960565)
          ·
            refine ⟨5841758122477819273308803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62312086639763405581960565 5841758122477819273308803)
            ·
              refine ⟨8762637183716728909963205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841758122477819273308803 8762637183716728909963205)
              ·
                refine ⟨1642994471946886670618101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8762637183716728909963205 1642994471946886670618101)
                ·
                  refine ⟨154030731745020625370447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1642994471946886670618101 154030731745020625370447)
                  ·
                    rfl

theorem cell22_1349882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_1349882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349882 prefixEnd_1349882 := by exact prefixLift 1349882
  have htrace : WordTrace (prefixWord ++ tailWord_1349882) baseStart_1349882 baseEnd_1349882 := by
    simpa [prefixWord, tailWord_1349882, baseEnd_1349882] using wordTrace_append hprefix tailTrace_1349882
  have hstable : (prefixWord ++ tailWord_1349882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349882).length < 2 ^ (prefixWord ++ tailWord_1349882).sum := by decide
  have hdescent : baseEnd_1349882 < baseStart_1349882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349897 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_1349897 : Nat := 118140960795 + 1349897 * 2 ^ 59
def prefixEnd_1349897 : Nat := 4983230072969 + 3 ^ 40 * 1349897 * 2
def baseEnd_1349897 : Nat := 462097330041606836986295

theorem tailTrace_1349897 : CollatzResearch.WordTrace tailWord_1349897 prefixEnd_1349897 462097330041606836986295 := by
  unfold tailWord_1349897
  simp only [CollatzResearch.WordTrace]
  refine ⟨49234788390561187898159945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32823192260374125265439963 49234788390561187898159945)
  ·
    refine ⟨36926091292920890923619959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49234788390561187898159945 36926091292920890923619959)
    ·
      refine ⟨55389136939381336385429939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36926091292920890923619959 55389136939381336385429939)
      ·
        refine ⟨83083705409072004578144909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55389136939381336385429939 83083705409072004578144909)
        ·
          refine ⟨31156389528402001716804341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83083705409072004578144909 31156389528402001716804341)
          ·
            refine ⟨2920911518287687660950407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31156389528402001716804341 2920911518287687660950407)
            ·
              refine ⟨4381367277431531491425611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920911518287687660950407 4381367277431531491425611)
              ·
                refine ⟨6572050916147297237138417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381367277431531491425611 6572050916147297237138417)
                ·
                  refine ⟨4929038187110472927853813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6572050916147297237138417 4929038187110472927853813)
                  ·
                    refine ⟨462097330041606836986295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4929038187110472927853813 462097330041606836986295)
                    ·
                      rfl

theorem cell22_1349897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_1349897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349897 prefixEnd_1349897 := by exact prefixLift 1349897
  have htrace : WordTrace (prefixWord ++ tailWord_1349897) baseStart_1349897 baseEnd_1349897 := by
    simpa [prefixWord, tailWord_1349897, baseEnd_1349897] using wordTrace_append hprefix tailTrace_1349897
  have hstable : (prefixWord ++ tailWord_1349897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349897).length < 2 ^ (prefixWord ++ tailWord_1349897).sum := by decide
  have hdescent : baseEnd_1349897 < baseStart_1349897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349912 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1349912 : Nat := 118140960795 + 1349912 * 2 ^ 59
def prefixEnd_1349912 : Nat := 4983230072969 + 3 ^ 40 * 1349912 * 2
def baseEnd_1349912 : Nat := 462102464848151797861249

theorem tailTrace_1349912 : CollatzResearch.WordTrace tailWord_1349912 prefixEnd_1349912 462102464848151797861249 := by
  unfold tailWord_1349912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617667742753422729977995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32823556990337896973303993 24617667742753422729977995)
  ·
    refine ⟨36926501614130134094966993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24617667742753422729977995 36926501614130134094966993)
    ·
      refine ⟨27694876210597600571225245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36926501614130134094966993 27694876210597600571225245)
      ·
        refine ⟨10385578578974100214209467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27694876210597600571225245 10385578578974100214209467)
        ·
          refine ⟨15578367868461150321314201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385578578974100214209467 15578367868461150321314201)
          ·
            refine ⟨11683775901345862740985651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15578367868461150321314201 11683775901345862740985651)
            ·
              refine ⟨17525663852018794111478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683775901345862740985651 17525663852018794111478477)
              ·
                refine ⟨6572123944507047791804429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17525663852018794111478477 6572123944507047791804429)
                ·
                  refine ⟨2464546479190142921926661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6572123944507047791804429 2464546479190142921926661)
                  ·
                    refine ⟨462102464848151797861249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464546479190142921926661 462102464848151797861249)
                    ·
                      rfl

theorem cell22_1349912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1349912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349912 prefixEnd_1349912 := by exact prefixLift 1349912
  have htrace : WordTrace (prefixWord ++ tailWord_1349912) baseStart_1349912 baseEnd_1349912 := by
    simpa [prefixWord, tailWord_1349912, baseEnd_1349912] using wordTrace_append hprefix tailTrace_1349912
  have hstable : (prefixWord ++ tailWord_1349912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349912).length < 2 ^ (prefixWord ++ tailWord_1349912).sum := by decide
  have hdescent : baseEnd_1349912 < baseStart_1349912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349933 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1349933 : Nat := 118140960795 + 1349933 * 2 ^ 59
def prefixEnd_1349933 : Nat := 4983230072969 + 3 ^ 40 * 1349933 * 2
def baseEnd_1349933 : Nat := 154036551192438247695395

theorem tailTrace_1349933 : CollatzResearch.WordTrace tailWord_1349933 prefixEnd_1349933 154036551192438247695395 := by
  unfold tailWord_1349933
  simp only [CollatzResearch.WordTrace]
  refine ⟨49236101418430766046470453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32824067612287177364313635 49236101418430766046470453)
  ·
    refine ⟨4615884507977884316856605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49236101418430766046470453 4615884507977884316856605)
    ·
      refine ⟨1730956690491706618821227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4615884507977884316856605 1730956690491706618821227)
      ·
        refine ⟨2596435035737559928231841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730956690491706618821227 2596435035737559928231841)
        ·
          refine ⟨1947326276803169946173881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596435035737559928231841 1947326276803169946173881)
          ·
            refine ⟨1460494707602377459630411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947326276803169946173881 1460494707602377459630411)
            ·
              refine ⟨2190742061403566189445617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460494707602377459630411 2190742061403566189445617)
              ·
                refine ⟨1643056546052674642084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190742061403566189445617 1643056546052674642084213)
                ·
                  refine ⟨154036551192438247695395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643056546052674642084213 154036551192438247695395)
                  ·
                    rfl

theorem cell22_1349933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1349933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349933 prefixEnd_1349933 := by exact prefixLift 1349933
  have htrace : WordTrace (prefixWord ++ tailWord_1349933) baseStart_1349933 baseEnd_1349933 := by
    simpa [prefixWord, tailWord_1349933, baseEnd_1349933] using wordTrace_append hprefix tailTrace_1349933
  have hstable : (prefixWord ++ tailWord_1349933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349933).length < 2 ^ (prefixWord ++ tailWord_1349933).sum := by decide
  have hdescent : baseEnd_1349933 < baseStart_1349933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349944 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_1349944 : Nat := 118140960795 + 1349944 * 2 ^ 59
def prefixEnd_1349944 : Nat := 4983230072969 + 3 ^ 40 * 1349944 * 2
def baseEnd_1349944 : Nat := 154037806367371460353717

theorem tailTrace_1349944 : CollatzResearch.WordTrace tailWord_1349944 prefixEnd_1349944 154037806367371460353717 := by
  unfold tailWord_1349944
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618251310695457462560443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32824335080927276616747257 24618251310695457462560443)
  ·
    refine ⟨36927376966043186193840665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618251310695457462560443 36927376966043186193840665)
    ·
      refine ⟨27695532724532389645380499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36927376966043186193840665 27695532724532389645380499)
      ·
        refine ⟨41543299086798584468070749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27695532724532389645380499 41543299086798584468070749)
        ·
          refine ⟨15578737157549469175526531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41543299086798584468070749 15578737157549469175526531)
          ·
            refine ⟨23368105736324203763289797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15578737157549469175526531 23368105736324203763289797)
            ·
              refine ⟨4381519825560788205616837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23368105736324203763289797 4381519825560788205616837)
              ·
                refine ⟨821534967292647788553157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4381519825560788205616837 821534967292647788553157)
                ·
                  refine ⟨154037806367371460353717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 821534967292647788553157 154037806367371460353717)
                  ·
                    rfl

theorem cell22_1349944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_1349944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1349944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1349944 prefixEnd_1349944 := by exact prefixLift 1349944
  have htrace : WordTrace (prefixWord ++ tailWord_1349944) baseStart_1349944 baseEnd_1349944 := by
    simpa [prefixWord, tailWord_1349944, baseEnd_1349944] using wordTrace_append hprefix tailTrace_1349944
  have hstable : (prefixWord ++ tailWord_1349944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349944).length < 2 ^ (prefixWord ++ tailWord_1349944).sum := by decide
  have hdescent : baseEnd_1349944 < baseStart_1349944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350055 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1350055 : Nat := 118140960795 + 1350055 * 2 ^ 59
def prefixEnd_1350055 : Nat := 4983230072969 + 3 ^ 40 * 1350055 * 2
def baseEnd_1350055 : Nat := 462151416670547091535811

theorem tailTrace_1350055 : CollatzResearch.WordTrace tailWord_1350055 prefixEnd_1350055 462151416670547091535811 := by
  unfold tailWord_1350055
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240551123988780882411619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32827034082659187254941079 49240551123988780882411619)
  ·
    refine ⟨73860826685983171323617429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49240551123988780882411619 73860826685983171323617429)
    ·
      refine ⟨3462226250905461155794567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73860826685983171323617429 3462226250905461155794567)
      ·
        refine ⟨5193339376358191733691851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462226250905461155794567 5193339376358191733691851)
        ·
          refine ⟨7790009064537287600537777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193339376358191733691851 7790009064537287600537777)
          ·
            refine ⟨5842506798402965700403333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790009064537287600537777 5842506798402965700403333)
            ·
              refine ⟨1095470024700556068825625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5842506798402965700403333 1095470024700556068825625)
              ·
                refine ⟨821602518525417051619219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095470024700556068825625 821602518525417051619219)
                ·
                  refine ⟨1232403777788125577428829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821602518525417051619219 1232403777788125577428829)
                  ·
                    refine ⟨462151416670547091535811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232403777788125577428829 462151416670547091535811)
                    ·
                      rfl

theorem cell22_1350055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1350055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350055 prefixEnd_1350055 := by exact prefixLift 1350055
  have htrace : WordTrace (prefixWord ++ tailWord_1350055) baseStart_1350055 baseEnd_1350055 := by
    simpa [prefixWord, tailWord_1350055, baseEnd_1350055] using wordTrace_append hprefix tailTrace_1350055
  have hstable : (prefixWord ++ tailWord_1350055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350055).length < 2 ^ (prefixWord ++ tailWord_1350055).sum := by decide
  have hdescent : baseEnd_1350055 < baseStart_1350055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350111 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 4, 3]
def baseStart_1350111 : Nat := 118140960795 + 1350111 * 2 ^ 59
def prefixEnd_1350111 : Nat := 4983230072969 + 3 ^ 40 * 1350111 * 2
def baseEnd_1350111 : Nat := 462170586614981612135639

theorem tailTrace_1350111 : CollatzResearch.WordTrace tailWord_1350111 prefixEnd_1350111 462170586614981612135639 := by
  unfold tailWord_1350111
  simp only [CollatzResearch.WordTrace]
  refine ⟨49242593611785902446450187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32828395741190601630966791 49242593611785902446450187)
  ·
    refine ⟨73863890417678853669675281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49242593611785902446450187 73863890417678853669675281)
    ·
      refine ⟨55397917813259140252256461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73863890417678853669675281 55397917813259140252256461)
      ·
        refine ⟨20774219179972177594596173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55397917813259140252256461 20774219179972177594596173)
        ·
          refine ⟨7790332192489566597973565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20774219179972177594596173 7790332192489566597973565)
          ·
            refine ⟨2921374572183587474240087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7790332192489566597973565 2921374572183587474240087)
            ·
              refine ⟨4382061858275381211360131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921374572183587474240087 4382061858275381211360131)
              ·
                refine ⟨6573092787413071817040197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382061858275381211360131 6573092787413071817040197)
                ·
                  refine ⟨1232454897639950965695037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6573092787413071817040197 1232454897639950965695037)
                  ·
                    refine ⟨462170586614981612135639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232454897639950965695037 462170586614981612135639)
                    ·
                      rfl

theorem cell22_1350111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_1350111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350111 prefixEnd_1350111 := by exact prefixLift 1350111
  have htrace : WordTrace (prefixWord ++ tailWord_1350111) baseStart_1350111 baseEnd_1350111 := by
    simpa [prefixWord, tailWord_1350111, baseEnd_1350111] using wordTrace_append hprefix tailTrace_1350111
  have hstable : (prefixWord ++ tailWord_1350111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350111).length < 2 ^ (prefixWord ++ tailWord_1350111).sum := by decide
  have hdescent : baseEnd_1350111 < baseStart_1350111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350128 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_1350128 : Nat := 118140960795 + 1350128 * 2 ^ 59
def prefixEnd_1350128 : Nat := 4983230072969 + 3 ^ 40 * 1350128 * 2
def baseEnd_1350128 : Nat := 462176406062399234460587

theorem tailTrace_1350128 : CollatzResearch.WordTrace tailWord_1350128 prefixEnd_1350128 462176406062399234460587 := by
  unfold tailWord_1350128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621606826362157174909519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32828809101816209566546025 24621606826362157174909519)
  ·
    refine ⟨36932410239543235762364279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24621606826362157174909519 36932410239543235762364279)
    ·
      refine ⟨55398615359314853643546419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36932410239543235762364279 55398615359314853643546419)
      ·
        refine ⟨83097923038972280465319629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55398615359314853643546419 83097923038972280465319629)
        ·
          refine ⟨31161721139614605174494861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83097923038972280465319629 31161721139614605174494861)
          ·
            refine ⟨11685645427355476940435573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31161721139614605174494861 11685645427355476940435573)
            ·
              refine ⟨1095529258814575963165835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11685645427355476940435573 1095529258814575963165835)
              ·
                refine ⟨1643293888221863944748753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095529258814575963165835 1643293888221863944748753)
                ·
                  refine ⟨1232470416166397958561565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643293888221863944748753 1232470416166397958561565)
                  ·
                    refine ⟨462176406062399234460587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232470416166397958561565 462176406062399234460587)
                    ·
                      rfl

theorem cell22_1350128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_1350128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350128 prefixEnd_1350128 := by exact prefixLift 1350128
  have htrace : WordTrace (prefixWord ++ tailWord_1350128) baseStart_1350128 baseEnd_1350128 := by
    simpa [prefixWord, tailWord_1350128, baseEnd_1350128] using wordTrace_append hprefix tailTrace_1350128
  have hstable : (prefixWord ++ tailWord_1350128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350128).length < 2 ^ (prefixWord ++ tailWord_1350128).sum := by decide
  have hdescent : baseEnd_1350128 < baseStart_1350128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350173 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1350173 : Nat := 118140960795 + 1350173 * 2 ^ 59
def prefixEnd_1350173 : Nat := 4983230072969 + 3 ^ 40 * 1350173 * 2
def baseEnd_1350173 : Nat := 462191810482034117085449

theorem tailTrace_1350173 : CollatzResearch.WordTrace tailWord_1350173 prefixEnd_1350173 462191810482034117085449 := by
  unfold tailWord_1350173
  simp only [CollatzResearch.WordTrace]
  refine ⟨49244854937561287035207173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32829903291707524690138115 49244854937561287035207173)
  ·
    refine ⟨9233410300792741319101345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49244854937561287035207173 9233410300792741319101345)
    ·
      refine ⟨6925057725594555989326009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9233410300792741319101345 6925057725594555989326009)
      ·
        refine ⟨5193793294195916991994507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6925057725594555989326009 5193793294195916991994507)
        ·
          refine ⟨7790689941293875487991761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193793294195916991994507 7790689941293875487991761)
          ·
            refine ⟨5843017455970406615993821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7790689941293875487991761 5843017455970406615993821)
            ·
              refine ⟨2191131545988902480997683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5843017455970406615993821 2191131545988902480997683)
              ·
                refine ⟨3286697318983353721496525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191131545988902480997683 3286697318983353721496525)
                ·
                  refine ⟨1232511494618757645561197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3286697318983353721496525 1232511494618757645561197)
                  ·
                    refine ⟨462191810482034117085449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232511494618757645561197 462191810482034117085449)
                    ·
                      rfl

theorem cell22_1350173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1350173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350173 prefixEnd_1350173 := by exact prefixLift 1350173
  have htrace : WordTrace (prefixWord ++ tailWord_1350173) baseStart_1350173 baseEnd_1350173 := by
    simpa [prefixWord, tailWord_1350173, baseEnd_1350173] using wordTrace_append hprefix tailTrace_1350173
  have hstable : (prefixWord ++ tailWord_1350173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350173).length < 2 ^ (prefixWord ++ tailWord_1350173).sum := by decide
  have hdescent : baseEnd_1350173 < baseStart_1350173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350216 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1350216 : Nat := 118140960795 + 1350216 * 2 ^ 59
def prefixEnd_1350216 : Nat := 4983230072969 + 3 ^ 40 * 1350216 * 2
def baseEnd_1350216 : Nat := 462206530260796338260317

theorem tailTrace_1350216 : CollatzResearch.WordTrace tailWord_1350216 prefixEnd_1350216 462206530260796338260317 := by
  unfold tailWord_1350216
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623211638202752689511251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32830948850937003586015001 24623211638202752689511251)
  ·
    refine ⟨36934817457304129034266877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24623211638202752689511251 36934817457304129034266877)
    ·
      refine ⟨13850556546489048387850079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36934817457304129034266877 13850556546489048387850079)
      ·
        refine ⟨20775834819733572581775119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13850556546489048387850079 20775834819733572581775119)
        ·
          refine ⟨31163752229600358872662679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20775834819733572581775119 31163752229600358872662679)
          ·
            refine ⟨46745628344400538308994019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31163752229600358872662679 46745628344400538308994019)
            ·
              refine ⟨70118442516600807463491029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46745628344400538308994019 70118442516600807463491029)
              ·
                refine ⟨1643400996482831424925571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70118442516600807463491029 1643400996482831424925571)
                ·
                  refine ⟨2465101494724247137388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643400996482831424925571 2465101494724247137388357)
                  ·
                    refine ⟨462206530260796338260317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465101494724247137388357 462206530260796338260317)
                    ·
                      rfl

theorem cell22_1350216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1350216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350216 prefixEnd_1350216 := by exact prefixLift 1350216
  have htrace : WordTrace (prefixWord ++ tailWord_1350216) baseStart_1350216 baseEnd_1350216 := by
    simpa [prefixWord, tailWord_1350216, baseEnd_1350216] using wordTrace_append hprefix tailTrace_1350216
  have hstable : (prefixWord ++ tailWord_1350216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350216).length < 2 ^ (prefixWord ++ tailWord_1350216).sum := by decide
  have hdescent : baseEnd_1350216 < baseStart_1350216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350248 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_1350248 : Nat := 118140960795 + 1350248 * 2 ^ 59
def prefixEnd_1350248 : Nat := 4983230072969 + 3 ^ 40 * 1350248 * 2
def baseEnd_1350248 : Nat := 154072494838252973820073

theorem tailTrace_1350248 : CollatzResearch.WordTrace tailWord_1350248 prefixEnd_1350248 154072494838252973820073 := by
  unfold tailWord_1350248
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623795206144787422093699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32831726941526383229458265 24623795206144787422093699)
  ·
    refine ⟨36935692809217181133140549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24623795206144787422093699 36935692809217181133140549)
    ·
      refine ⟨6925442401728221462463853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36935692809217181133140549 6925442401728221462463853)
      ·
        refine ⟨2597040900648083048423945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6925442401728221462463853 2597040900648083048423945)
        ·
          refine ⟨1947780675486062286317959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597040900648083048423945 1947780675486062286317959)
          ·
            refine ⟨2921671013229093429476939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947780675486062286317959 2921671013229093429476939)
            ·
              refine ⟨4382506519843640144215409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921671013229093429476939 4382506519843640144215409)
              ·
                refine ⟨3286879889882730108161557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382506519843640144215409 3286879889882730108161557)
                ·
                  refine ⟨154072494838252973820073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3286879889882730108161557 154072494838252973820073)
                  ·
                    rfl

theorem cell22_1350248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_1350248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350248 prefixEnd_1350248 := by exact prefixLift 1350248
  have htrace : WordTrace (prefixWord ++ tailWord_1350248) baseStart_1350248 baseEnd_1350248 := by
    simpa [prefixWord, tailWord_1350248, baseEnd_1350248] using wordTrace_append hprefix tailTrace_1350248
  have hstable : (prefixWord ++ tailWord_1350248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350248).length < 2 ^ (prefixWord ++ tailWord_1350248).sum := by decide
  have hdescent : baseEnd_1350248 < baseStart_1350248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350276 : List Nat := [2, 3, 2, 1, 3, 2, 9]
def baseStart_1350276 : Nat := 118140960795 + 1350276 * 2 ^ 59
def prefixEnd_1350276 : Nat := 4983230072969 + 3 ^ 40 * 1350276 * 2
def baseEnd_1350276 : Nat := 17119521092110228954079

theorem tailTrace_1350276 : CollatzResearch.WordTrace tailWord_1350276 prefixEnd_1350276 17119521092110228954079 := by
  unfold tailWord_1350276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24624305828094067813103341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32832407770792090417471121 24624305828094067813103341)
  ·
    refine ⟨9234114685535275429913753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24624305828094067813103341 9234114685535275429913753)
    ·
      refine ⟨6925586014151456572435315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9234114685535275429913753 6925586014151456572435315)
      ·
        refine ⟨10388379021227184858652973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925586014151456572435315 10388379021227184858652973)
        ·
          refine ⟨3895642132960194321994865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10388379021227184858652973 3895642132960194321994865)
          ·
            refine ⟨2921731599720145741496149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3895642132960194321994865 2921731599720145741496149)
            ·
              refine ⟨17119521092110228954079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2921731599720145741496149 17119521092110228954079)
              ·
                rfl

theorem cell22_1350276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 9].length) (baseStart_1350276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350276 prefixEnd_1350276 := by exact prefixLift 1350276
  have htrace : WordTrace (prefixWord ++ tailWord_1350276) baseStart_1350276 baseEnd_1350276 := by
    simpa [prefixWord, tailWord_1350276, baseEnd_1350276] using wordTrace_append hprefix tailTrace_1350276
  have hstable : (prefixWord ++ tailWord_1350276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350276).length < 2 ^ (prefixWord ++ tailWord_1350276).sum := by decide
  have hdescent : baseEnd_1350276 < baseStart_1350276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350291 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 7, 3]
def baseStart_1350291 : Nat := 118140960795 + 1350291 * 2 ^ 59
def prefixEnd_1350291 : Nat := 4983230072969 + 3 ^ 40 * 1350291 * 2
def baseEnd_1350291 : Nat := 462232204293521142635087

theorem tailTrace_1350291 : CollatzResearch.WordTrace tailWord_1350291 prefixEnd_1350291 462232204293521142635087 := by
  unfold tailWord_1350291
  simp only [CollatzResearch.WordTrace]
  refine ⟨49249158751133793188002727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32832772500755862125335151 49249158751133793188002727)
  ·
    refine ⟨73873738126700689782004091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49249158751133793188002727 73873738126700689782004091)
    ·
      refine ⟨110810607190051034673006137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73873738126700689782004091 110810607190051034673006137)
      ·
        refine ⟨83107955392538276004754603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110810607190051034673006137 83107955392538276004754603)
        ·
          refine ⟨124661933088807414007131905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83107955392538276004754603 124661933088807414007131905)
          ·
            refine ⟨93496449816605560505348929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124661933088807414007131905 93496449816605560505348929)
            ·
              refine ⟨70122337362454170379011697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93496449816605560505348929 70122337362454170379011697)
              ·
                refine ⟨52591753021840627784258773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70122337362454170379011697 52591753021840627784258773)
                ·
                  refine ⟨1232619211449389713693565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52591753021840627784258773 1232619211449389713693565)
                  ·
                    refine ⟨462232204293521142635087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232619211449389713693565 462232204293521142635087)
                    ·
                      rfl

theorem cell22_1350291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 3].length) (baseStart_1350291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350291 prefixEnd_1350291 := by exact prefixLift 1350291
  have htrace : WordTrace (prefixWord ++ tailWord_1350291) baseStart_1350291 baseEnd_1350291 := by
    simpa [prefixWord, tailWord_1350291, baseEnd_1350291] using wordTrace_append hprefix tailTrace_1350291
  have hstable : (prefixWord ++ tailWord_1350291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350291).length < 2 ^ (prefixWord ++ tailWord_1350291).sum := by decide
  have hdescent : baseEnd_1350291 < baseStart_1350291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350308 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1350308 : Nat := 118140960795 + 1350308 * 2 ^ 59
def prefixEnd_1350308 : Nat := 4983230072969 + 3 ^ 40 * 1350308 * 2
def baseEnd_1350308 : Nat := 462238023740938764960035

theorem tailTrace_1350308 : CollatzResearch.WordTrace tailWord_1350308 prefixEnd_1350308 462238023740938764960035 := by
  unfold tailWord_1350308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24624889396036102545685789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32833185861381470060914385 24624889396036102545685789)
  ·
    refine ⟨9234333523513538454632171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24624889396036102545685789 9234333523513538454632171)
    ·
      refine ⟨13851500285270307681948257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9234333523513538454632171 13851500285270307681948257)
      ·
        refine ⟨10388625213952730761461193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13851500285270307681948257 10388625213952730761461193)
        ·
          refine ⟨7791468910464548071095895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10388625213952730761461193 7791468910464548071095895)
          ·
            refine ⟨11687203365696822106643843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791468910464548071095895 11687203365696822106643843)
            ·
              refine ⟨17530805048545233159965765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687203365696822106643843 17530805048545233159965765)
              ·
                refine ⟨3287025946602231217493581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17530805048545233159965765 3287025946602231217493581)
                ·
                  refine ⟨1232634729975836706560093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3287025946602231217493581 1232634729975836706560093)
                  ·
                    refine ⟨462238023740938764960035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232634729975836706560093 462238023740938764960035)
                    ·
                      rfl

theorem cell22_1350308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1350308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350308 prefixEnd_1350308 := by exact prefixLift 1350308
  have htrace : WordTrace (prefixWord ++ tailWord_1350308) baseStart_1350308 baseEnd_1350308 := by
    simpa [prefixWord, tailWord_1350308, baseEnd_1350308] using wordTrace_append hprefix tailTrace_1350308
  have hstable : (prefixWord ++ tailWord_1350308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350308).length < 2 ^ (prefixWord ++ tailWord_1350308).sum := by decide
  have hdescent : baseEnd_1350308 < baseStart_1350308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350385 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_1350385 : Nat := 118140960795 + 1350385 * 2 ^ 59
def prefixEnd_1350385 : Nat := 4983230072969 + 3 ^ 40 * 1350385 * 2
def baseEnd_1350385 : Nat := 462264382414536230784799

theorem tailTrace_1350385 : CollatzResearch.WordTrace tailWord_1350385 prefixEnd_1350385 462264382414536230784799 := by
  unfold tailWord_1350385
  simp only [CollatzResearch.WordTrace]
  refine ⟨49252587212793247241924609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32835058141862164827949739 49252587212793247241924609)
  ·
    refine ⟨36939440409594935431443457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49252587212793247241924609 36939440409594935431443457)
    ·
      refine ⟨27704580307196201573582593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36939440409594935431443457 27704580307196201573582593)
      ·
        refine ⟨20778435230397151180186945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27704580307196201573582593 20778435230397151180186945)
        ·
          refine ⟨15583826422797863385140209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20778435230397151180186945 15583826422797863385140209)
          ·
            refine ⟨11687869817098397538855157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15583826422797863385140209 11687869817098397538855157)
            ·
              refine ⟨1095737795352974769267671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11687869817098397538855157 1095737795352974769267671)
              ·
                refine ⟨1643606693029462153901507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095737795352974769267671 1643606693029462153901507)
                ·
                  refine ⟨2465410039544193230852261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643606693029462153901507 2465410039544193230852261)
                  ·
                    refine ⟨462264382414536230784799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465410039544193230852261 462264382414536230784799)
                    ·
                      rfl

theorem cell22_1350385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_1350385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350385 prefixEnd_1350385 := by exact prefixLift 1350385
  have htrace : WordTrace (prefixWord ++ tailWord_1350385) baseStart_1350385 baseEnd_1350385 := by
    simpa [prefixWord, tailWord_1350385, baseEnd_1350385] using wordTrace_append hprefix tailTrace_1350385
  have hstable : (prefixWord ++ tailWord_1350385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350385).length < 2 ^ (prefixWord ++ tailWord_1350385).sum := by decide
  have hdescent : baseEnd_1350385 < baseStart_1350385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350389 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 5]
def baseStart_1350389 : Nat := 118140960795 + 1350389 * 2 ^ 59
def prefixEnd_1350389 : Nat := 4983230072969 + 3 ^ 40 * 1350389 * 2
def baseEnd_1350389 : Nat := 154088583898760517894929

theorem tailTrace_1350389 : CollatzResearch.WordTrace tailWord_1350389 prefixEnd_1350389 154088583898760517894929 := by
  unfold tailWord_1350389
  simp only [CollatzResearch.WordTrace]
  refine ⟨49252733104778755925070221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32835155403185837283380147 49252733104778755925070221)
  ·
    refine ⟨18469774914292033471901333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49252733104778755925070221 18469774914292033471901333)
    ·
      refine ⟨865770699107439068995375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18469774914292033471901333 865770699107439068995375)
      ·
        refine ⟨1298656048661158603493063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865770699107439068995375 1298656048661158603493063)
        ·
          refine ⟨1947984072991737905239595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298656048661158603493063 1947984072991737905239595)
          ·
            refine ⟨2921976109487606857859393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947984072991737905239595 2921976109487606857859393)
            ·
              refine ⟨2191482082115705143394545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921976109487606857859393 2191482082115705143394545)
              ·
                refine ⟨1643611561586778857545909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191482082115705143394545 1643611561586778857545909)
                ·
                  refine ⟨154088583898760517894929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1643611561586778857545909 154088583898760517894929)
                  ·
                    rfl

theorem cell22_1350389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_1350389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350389 prefixEnd_1350389 := by exact prefixLift 1350389
  have htrace : WordTrace (prefixWord ++ tailWord_1350389) baseStart_1350389 baseEnd_1350389 := by
    simpa [prefixWord, tailWord_1350389, baseEnd_1350389] using wordTrace_append hprefix tailTrace_1350389
  have hstable : (prefixWord ++ tailWord_1350389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350389).length < 2 ^ (prefixWord ++ tailWord_1350389).sum := by decide
  have hdescent : baseEnd_1350389 < baseStart_1350389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350441 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1350441 : Nat := 118140960795 + 1350441 * 2 ^ 59
def prefixEnd_1350441 : Nat := 4983230072969 + 3 ^ 40 * 1350441 * 2
def baseEnd_1350441 : Nat := 462283552358970751384627

theorem tailTrace_1350441 : CollatzResearch.WordTrace tailWord_1350441 prefixEnd_1350441 462283552358970751384627 := by
  unfold tailWord_1350441
  simp only [CollatzResearch.WordTrace]
  refine ⟨49254629700590368805963177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32836419800393579203975451 49254629700590368805963177)
  ·
    refine ⟨36940972275442776604472383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49254629700590368805963177 36940972275442776604472383)
    ·
      refine ⟨55411458413164164906708575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36940972275442776604472383 55411458413164164906708575)
      ·
        refine ⟨83117187619746247360062863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55411458413164164906708575 83117187619746247360062863)
        ·
          refine ⟨124675781429619371040094295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83117187619746247360062863 124675781429619371040094295)
          ·
            refine ⟨187013672144429056560141443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124675781429619371040094295 187013672144429056560141443)
            ·
              refine ⟨280520508216643584840212165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187013672144429056560141443 280520508216643584840212165)
              ·
                refine ⟨52597595290620672157539781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280520508216643584840212165 52597595290620672157539781)
                ·
                  refine ⟨9862049116991376029538709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52597595290620672157539781 9862049116991376029538709)
                  ·
                    refine ⟨462283552358970751384627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9862049116991376029538709 462283552358970751384627)
                    ·
                      rfl

theorem cell22_1350441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1350441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350441 prefixEnd_1350441 := by exact prefixLift 1350441
  have htrace : WordTrace (prefixWord ++ tailWord_1350441) baseStart_1350441 baseEnd_1350441 := by
    simpa [prefixWord, tailWord_1350441, baseEnd_1350441] using wordTrace_append hprefix tailTrace_1350441
  have hstable : (prefixWord ++ tailWord_1350441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350441).length < 2 ^ (prefixWord ++ tailWord_1350441).sum := by decide
  have hdescent : baseEnd_1350441 < baseStart_1350441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350537 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 1, 4]
def baseStart_1350537 : Nat := 118140960795 + 1350537 * 2 ^ 59
def prefixEnd_1350537 : Nat := 4983230072969 + 3 ^ 40 * 1350537 * 2
def baseEnd_1350537 : Nat := 462316415120858500984333

theorem tailTrace_1350537 : CollatzResearch.WordTrace tailWord_1350537 prefixEnd_1350537 462316415120858500984333 := by
  unfold tailWord_1350537
  simp only [CollatzResearch.WordTrace]
  refine ⟨49258131108242577201457865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32838754072161718134305243 49258131108242577201457865)
  ·
    refine ⟨36943598331181932901093399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49258131108242577201457865 36943598331181932901093399)
    ·
      refine ⟨55415397496772899351640099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36943598331181932901093399 55415397496772899351640099)
      ·
        refine ⟨83123096245159349027460149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55415397496772899351640099 83123096245159349027460149)
        ·
          refine ⟨7792790272983688971324389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83123096245159349027460149 7792790272983688971324389)
          ·
            refine ⟨1461148176184441682123323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7792790272983688971324389 1461148176184441682123323)
            ·
              refine ⟨2191722264276662523184985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461148176184441682123323 2191722264276662523184985)
              ·
                refine ⟨1643791698207496892388739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191722264276662523184985 1643791698207496892388739)
                ·
                  refine ⟨2465687547311245338583109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643791698207496892388739 2465687547311245338583109)
                  ·
                    refine ⟨462316415120858500984333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465687547311245338583109 462316415120858500984333)
                    ·
                      rfl

theorem cell22_1350537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 4].length) (baseStart_1350537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350537 prefixEnd_1350537 := by exact prefixLift 1350537
  have htrace : WordTrace (prefixWord ++ tailWord_1350537) baseStart_1350537 baseEnd_1350537 := by
    simpa [prefixWord, tailWord_1350537, baseEnd_1350537] using wordTrace_append hprefix tailTrace_1350537
  have hstable : (prefixWord ++ tailWord_1350537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350537).length < 2 ^ (prefixWord ++ tailWord_1350537).sum := by decide
  have hdescent : baseEnd_1350537 < baseStart_1350537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350554 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_1350554 : Nat := 118140960795 + 1350554 * 2 ^ 59
def prefixEnd_1350554 : Nat := 4983230072969 + 3 ^ 40 * 1350554 * 2
def baseEnd_1350554 : Nat := 462322234568276123309281

theorem tailTrace_1350554 : CollatzResearch.WordTrace tailWord_1350554 prefixEnd_1350554 462322234568276123309281 := by
  unfold tailWord_1350554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314687787295247276206679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32839167432787326069884477 12314687787295247276206679)
  ·
    refine ⟨18472031680942870914310019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12314687787295247276206679 18472031680942870914310019)
    ·
      refine ⟨27708047521414306371465029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18472031680942870914310019 27708047521414306371465029)
      ·
        refine ⟨5195258910265182444649693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27708047521414306371465029 5195258910265182444649693)
        ·
          refine ⟨1948222091349443416743635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5195258910265182444649693 1948222091349443416743635)
          ·
            refine ⟨2922333137024165125115453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948222091349443416743635 2922333137024165125115453)
            ·
              refine ⟨1095874926384061921918295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922333137024165125115453 1095874926384061921918295)
              ·
                refine ⟨1643812389576092882877443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095874926384061921918295 1643812389576092882877443)
                ·
                  refine ⟨2465718584364139324316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643812389576092882877443 2465718584364139324316165)
                  ·
                    refine ⟨462322234568276123309281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465718584364139324316165 462322234568276123309281)
                    ·
                      rfl

theorem cell22_1350554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_1350554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350554 prefixEnd_1350554 := by exact prefixLift 1350554
  have htrace : WordTrace (prefixWord ++ tailWord_1350554) baseStart_1350554 baseEnd_1350554 := by
    simpa [prefixWord, tailWord_1350554, baseEnd_1350554] using wordTrace_append hprefix tailTrace_1350554
  have hstable : (prefixWord ++ tailWord_1350554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350554).length < 2 ^ (prefixWord ++ tailWord_1350554).sum := by decide
  have hdescent : baseEnd_1350554 < baseStart_1350554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1350578 : Nat := 118140960795 + 1350578 * 2 ^ 59
def prefixEnd_1350578 : Nat := 4983230072969 + 3 ^ 40 * 1350578 * 2
def baseEnd_1350578 : Nat := 462330450258748060709207

theorem tailTrace_1350578 : CollatzResearch.WordTrace tailWord_1350578 prefixEnd_1350578 462330450258748060709207 := by
  unfold tailWord_1350578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314906625273510300925097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32839751000729360802466925 12314906625273510300925097)
  ·
    refine ⟨9236179968955132725693823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12314906625273510300925097 9236179968955132725693823)
    ·
      refine ⟨13854269953432699088540735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236179968955132725693823 13854269953432699088540735)
      ·
        refine ⟨20781404930149048632811103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13854269953432699088540735 20781404930149048632811103)
        ·
          refine ⟨31172107395223572949216655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20781404930149048632811103 31172107395223572949216655)
          ·
            refine ⟨46758161092835359423824983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31172107395223572949216655 46758161092835359423824983)
            ·
              refine ⟨70137241639253039135737475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46758161092835359423824983 70137241639253039135737475)
              ·
                refine ⟨105205862458879558703606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70137241639253039135737475 105205862458879558703606213)
                ·
                  refine ⟨19726099211039917256926165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105205862458879558703606213 19726099211039917256926165)
                  ·
                    refine ⟨462330450258748060709207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19726099211039917256926165 462330450258748060709207)
                    ·
                      rfl

theorem cell22_1350578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1350578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350578 prefixEnd_1350578 := by exact prefixLift 1350578
  have htrace : WordTrace (prefixWord ++ tailWord_1350578) baseStart_1350578 baseEnd_1350578 := by
    simpa [prefixWord, tailWord_1350578, baseEnd_1350578] using wordTrace_append hprefix tailTrace_1350578
  have hstable : (prefixWord ++ tailWord_1350578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350578).length < 2 ^ (prefixWord ++ tailWord_1350578).sum := by decide
  have hdescent : baseEnd_1350578 < baseStart_1350578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350595 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 3, 3]
def baseStart_1350595 : Nat := 118140960795 + 1350595 * 2 ^ 59
def prefixEnd_1350595 : Nat := 4983230072969 + 3 ^ 40 * 1350595 * 2
def baseEnd_1350595 : Nat := 462336269706165683034155

theorem tailTrace_1350595 : CollatzResearch.WordTrace tailWord_1350595 prefixEnd_1350595 462336269706165683034155 := by
  unfold tailWord_1350595
  simp only [CollatzResearch.WordTrace]
  refine ⟨49260246542032453107069239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32840164361354968738046159 49260246542032453107069239)
  ·
    refine ⟨73890369813048679660603859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49260246542032453107069239 73890369813048679660603859)
    ·
      refine ⟨110835554719573019490905789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73890369813048679660603859 110835554719573019490905789)
      ·
        refine ⟨41563333019839882309089671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110835554719573019490905789 41563333019839882309089671)
        ·
          refine ⟨62344999529759823463634507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41563333019839882309089671 62344999529759823463634507)
          ·
            refine ⟨93517499294639735195451761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62344999529759823463634507 93517499294639735195451761)
            ·
              refine ⟨70138124470979801396588821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93517499294639735195451761 70138124470979801396588821)
              ·
                refine ⟨3287724584577178190465101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70138124470979801396588821 3287724584577178190465101)
                ·
                  refine ⟨1232896719216441821424413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3287724584577178190465101 1232896719216441821424413)
                  ·
                    refine ⟨462336269706165683034155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232896719216441821424413 462336269706165683034155)
                    ·
                      rfl

theorem cell22_1350595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 3].length) (baseStart_1350595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350595 prefixEnd_1350595 := by exact prefixLift 1350595
  have htrace : WordTrace (prefixWord ++ tailWord_1350595) baseStart_1350595 baseEnd_1350595 := by
    simpa [prefixWord, tailWord_1350595, baseEnd_1350595] using wordTrace_append hprefix tailTrace_1350595
  have hstable : (prefixWord ++ tailWord_1350595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350595).length < 2 ^ (prefixWord ++ tailWord_1350595).sum := by decide
  have hdescent : baseEnd_1350595 < baseStart_1350595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350605 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1350605 : Nat := 118140960795 + 1350605 * 2 ^ 59
def prefixEnd_1350605 : Nat := 4983230072969 + 3 ^ 40 * 1350605 * 2
def baseEnd_1350605 : Nat := 462339692910528990284125

theorem tailTrace_1350605 : CollatzResearch.WordTrace tailWord_1350605 prefixEnd_1350605 462339692910528990284125 := by
  unfold tailWord_1350605
  simp only [CollatzResearch.WordTrace]
  refine ⟨49260611271996224814933269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32840407514664149876622179 49260611271996224814933269)
  ·
    refine ⟨2309091153374823038199997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49260611271996224814933269 2309091153374823038199997)
    ·
      refine ⟨865909182515558639324999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2309091153374823038199997 865909182515558639324999)
      ·
        refine ⟨1298863773773337958987499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865909182515558639324999 1298863773773337958987499)
        ·
          refine ⟨1948295660660006938481249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298863773773337958987499 1948295660660006938481249)
          ·
            refine ⟨1461221745495005203860937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948295660660006938481249 1461221745495005203860937)
            ·
              refine ⟨1095916309121253902895703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461221745495005203860937 1095916309121253902895703)
              ·
                refine ⟨1643874463681880854343555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095916309121253902895703 1643874463681880854343555)
                ·
                  refine ⟨2465811695522821281515333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643874463681880854343555 2465811695522821281515333)
                  ·
                    refine ⟨462339692910528990284125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465811695522821281515333 462339692910528990284125)
                    ·
                      rfl

theorem cell22_1350605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1350605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350605 prefixEnd_1350605 := by exact prefixLift 1350605
  have htrace : WordTrace (prefixWord ++ tailWord_1350605) baseStart_1350605 baseEnd_1350605 := by
    simpa [prefixWord, tailWord_1350605, baseEnd_1350605] using wordTrace_append hprefix tailTrace_1350605
  have hstable : (prefixWord ++ tailWord_1350605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350605).length < 2 ^ (prefixWord ++ tailWord_1350605).sum := by decide
  have hdescent : baseEnd_1350605 < baseStart_1350605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350608 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_1350608 : Nat := 118140960795 + 1350608 * 2 ^ 59
def prefixEnd_1350608 : Nat := 4983230072969 + 3 ^ 40 * 1350608 * 2
def baseEnd_1350608 : Nat := 154113573290612660819705

theorem tailTrace_1350608 : CollatzResearch.WordTrace tailWord_1350608 prefixEnd_1350608 154113573290612660819705 := by
  unfold tailWord_1350608
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630360345492678163646239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32840480460656904218194985 24630360345492678163646239)
  ·
    refine ⟨36945540518239017245469359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24630360345492678163646239 36945540518239017245469359)
    ·
      refine ⟨55418310777358525868204039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36945540518239017245469359 55418310777358525868204039)
      ·
        refine ⟨83127466166037788802306059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55418310777358525868204039 83127466166037788802306059)
        ·
          refine ⟨124691199249056683203459089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83127466166037788802306059 124691199249056683203459089)
          ·
            refine ⟨93518399436792512402594317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124691199249056683203459089 93518399436792512402594317)
            ·
              refine ⟨35069399788797192150972869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93518399436792512402594317 35069399788797192150972869)
              ·
                refine ⟨6575512460399473528307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35069399788797192150972869 6575512460399473528307413)
                ·
                  refine ⟨154113573290612660819705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6575512460399473528307413 154113573290612660819705)
                  ·
                    rfl

theorem cell22_1350608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_1350608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350608 prefixEnd_1350608 := by exact prefixLift 1350608
  have htrace : WordTrace (prefixWord ++ tailWord_1350608) baseStart_1350608 baseEnd_1350608 := by
    simpa [prefixWord, tailWord_1350608, baseEnd_1350608] using wordTrace_append hprefix tailTrace_1350608
  have hstable : (prefixWord ++ tailWord_1350608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350608).length < 2 ^ (prefixWord ++ tailWord_1350608).sum := by decide
  have hdescent : baseEnd_1350608 < baseStart_1350608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350687 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 6]
def baseStart_1350687 : Nat := 118140960795 + 1350687 * 2 ^ 59
def prefixEnd_1350687 : Nat := 4983230072969 + 3 ^ 40 * 1350687 * 2
def baseEnd_1350687 : Nat := 154122587728769369911291

theorem tailTrace_1350687 : CollatzResearch.WordTrace tailWord_1350687 prefixEnd_1350687 154122587728769369911291 := by
  unfold tailWord_1350687
  simp only [CollatzResearch.WordTrace]
  refine ⟨49263602057699152819418315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32842401371799435212945543 49263602057699152819418315)
  ·
    refine ⟨73895403086548729229127473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49263602057699152819418315 73895403086548729229127473)
    ·
      refine ⟨55421552314911546921845605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73895403086548729229127473 55421552314911546921845605)
      ·
        refine ⟨10391541059045915047846051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55421552314911546921845605 10391541059045915047846051)
        ·
          refine ⟨15587311588568872571769077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391541059045915047846051 15587311588568872571769077)
          ·
            refine ⟨1461310461428331803603351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15587311588568872571769077 1461310461428331803603351)
            ·
              refine ⟨2191965692142497705405027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461310461428331803603351 2191965692142497705405027)
              ·
                refine ⟨3287948538213746558107541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191965692142497705405027 3287948538213746558107541)
                ·
                  refine ⟨154122587728769369911291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3287948538213746558107541 154122587728769369911291)
                  ·
                    rfl

theorem cell22_1350687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].length) (baseStart_1350687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350687 prefixEnd_1350687 := by exact prefixLift 1350687
  have htrace : WordTrace (prefixWord ++ tailWord_1350687) baseStart_1350687 baseEnd_1350687 := by
    simpa [prefixWord, tailWord_1350687, baseEnd_1350687] using wordTrace_append hprefix tailTrace_1350687
  have hstable : (prefixWord ++ tailWord_1350687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350687).length < 2 ^ (prefixWord ++ tailWord_1350687).sum := by decide
  have hdescent : baseEnd_1350687 < baseStart_1350687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350700 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1350700 : Nat := 118140960795 + 1350700 * 2 ^ 59
def prefixEnd_1350700 : Nat := 4983230072969 + 3 ^ 40 * 1350700 * 2
def baseEnd_1350700 : Nat := 462372213351980409158833

theorem tailTrace_1350700 : CollatzResearch.WordTrace tailWord_1350700 prefixEnd_1350700 462372213351980409158833 := by
  unfold tailWord_1350700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24632038103326028019820777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32842717471101370693094369 24632038103326028019820777)
  ·
    refine ⟨18474028577494521014865583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24632038103326028019820777 18474028577494521014865583)
    ·
      refine ⟨27711042866241781522298375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18474028577494521014865583 27711042866241781522298375)
      ·
        refine ⟨41566564299362672283447563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27711042866241781522298375 41566564299362672283447563)
        ·
          refine ⟨62349846449044008425171345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41566564299362672283447563 62349846449044008425171345)
          ·
            refine ⟨46762384836783006318878509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62349846449044008425171345 46762384836783006318878509)
            ·
              refine ⟨17535894313793627369579441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46762384836783006318878509 17535894313793627369579441)
              ·
                refine ⟨13151920735345220527184581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17535894313793627369579441 13151920735345220527184581)
                ·
                  refine ⟨2465985137877228848847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13151920735345220527184581 2465985137877228848847109)
                  ·
                    refine ⟨462372213351980409158833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465985137877228848847109 462372213351980409158833)
                    ·
                      rfl

theorem cell22_1350700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1350700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350700 prefixEnd_1350700 := by exact prefixLift 1350700
  have htrace : WordTrace (prefixWord ++ tailWord_1350700) baseStart_1350700 baseEnd_1350700 := by
    simpa [prefixWord, tailWord_1350700, baseEnd_1350700] using wordTrace_append hprefix tailTrace_1350700
  have hstable : (prefixWord ++ tailWord_1350700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350700).length < 2 ^ (prefixWord ++ tailWord_1350700).sum := by decide
  have hdescent : baseEnd_1350700 < baseStart_1350700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350702 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1350702 : Nat := 118140960795 + 1350702 * 2 ^ 59
def prefixEnd_1350702 : Nat := 4983230072969 + 3 ^ 40 * 1350702 * 2
def baseEnd_1350702 : Nat := 462372897992853070608827

theorem tailTrace_1350702 : CollatzResearch.WordTrace tailWord_1350702 prefixEnd_1350702 462372897992853070608827 := by
  unfold tailWord_1350702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158018644080601297651795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32842766101763206920809573 6158018644080601297651795)
  ·
    refine ⟨9237027966120901946477693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6158018644080601297651795 9237027966120901946477693)
    ·
      refine ⟨3463885487295338229929135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9237027966120901946477693 3463885487295338229929135)
      ·
        refine ⟨5195828230943007344893703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463885487295338229929135 5195828230943007344893703)
        ·
          refine ⟨7793742346414511017340555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195828230943007344893703 7793742346414511017340555)
          ·
            refine ⟨11690613519621766526010833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793742346414511017340555 11690613519621766526010833)
            ·
              refine ⟨8767960139716324894508125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11690613519621766526010833 8767960139716324894508125)
              ·
                refine ⟨3287985052393621835440547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767960139716324894508125 3287985052393621835440547)
                ·
                  refine ⟨4931977578590432753160821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287985052393621835440547 4931977578590432753160821)
                  ·
                    refine ⟨462372897992853070608827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4931977578590432753160821 462372897992853070608827)
                    ·
                      rfl

theorem cell22_1350702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1350702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350702 prefixEnd_1350702 := by exact prefixLift 1350702
  have htrace : WordTrace (prefixWord ++ tailWord_1350702) baseStart_1350702 baseEnd_1350702 := by
    simpa [prefixWord, tailWord_1350702, baseEnd_1350702] using wordTrace_append hprefix tailTrace_1350702
  have hstable : (prefixWord ++ tailWord_1350702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350702).length < 2 ^ (prefixWord ++ tailWord_1350702).sum := by decide
  have hdescent : baseEnd_1350702 < baseStart_1350702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350717 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1350717 : Nat := 118140960795 + 1350717 * 2 ^ 59
def prefixEnd_1350717 : Nat := 4983230072969 + 3 ^ 40 * 1350717 * 2
def baseEnd_1350717 : Nat := 462378032799398031483781

theorem tailTrace_1350717 : CollatzResearch.WordTrace tailWord_1350717 prefixEnd_1350717 462378032799398031483781 := by
  unfold tailWord_1350717
  simp only [CollatzResearch.WordTrace]
  refine ⟨49264696247590467943010405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32843130831726978628673603 49264696247590467943010405)
  ·
    refine ⟨9237130546423212739314451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49264696247590467943010405 9237130546423212739314451)
    ·
      refine ⟨13855695819634819108971677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237130546423212739314451 13855695819634819108971677)
      ·
        refine ⟨5195885932363057165864379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13855695819634819108971677 5195885932363057165864379)
        ·
          refine ⟨7793828898544585748796569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195885932363057165864379 7793828898544585748796569)
          ·
            refine ⟨5845371673908439311597427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7793828898544585748796569 5845371673908439311597427)
            ·
              refine ⟨8768057510862658967396141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845371673908439311597427 8768057510862658967396141)
              ·
                refine ⟨3288021566573497112773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8768057510862658967396141 3288021566573497112773553)
                ·
                  refine ⟨2466016174930122834580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288021566573497112773553 2466016174930122834580165)
                  ·
                    refine ⟨462378032799398031483781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466016174930122834580165 462378032799398031483781)
                    ·
                      rfl

theorem cell22_1350717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1350717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350717 prefixEnd_1350717 := by exact prefixLift 1350717
  have htrace : WordTrace (prefixWord ++ tailWord_1350717) baseStart_1350717 baseEnd_1350717 := by
    simpa [prefixWord, tailWord_1350717, baseEnd_1350717] using wordTrace_append hprefix tailTrace_1350717
  have hstable : (prefixWord ++ tailWord_1350717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350717).length < 2 ^ (prefixWord ++ tailWord_1350717).sum := by decide
  have hdescent : baseEnd_1350717 < baseStart_1350717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350775 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1350775 : Nat := 118140960795 + 1350775 * 2 ^ 59
def prefixEnd_1350775 : Nat := 4983230072969 + 3 ^ 40 * 1350775 * 2
def baseEnd_1350775 : Nat := 462397887384705213533603

theorem tailTrace_1350775 : CollatzResearch.WordTrace tailWord_1350775 prefixEnd_1350775 462397887384705213533603 := by
  unfold tailWord_1350775
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266811681380343848621779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32844541120920229232414519 49266811681380343848621779)
  ·
    refine ⟨73900217522070515772932669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49266811681380343848621779 73900217522070515772932669)
    ·
      refine ⟨27712581570776443414849751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73900217522070515772932669 27712581570776443414849751)
      ·
        refine ⟨41568872356164665122274627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27712581570776443414849751 41568872356164665122274627)
        ·
          refine ⟨62353308534246997683411941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41568872356164665122274627 62353308534246997683411941)
          ·
            refine ⟨11691245350171312065639739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62353308534246997683411941 11691245350171312065639739)
            ·
              refine ⟨17536868025256968098459609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691245350171312065639739 17536868025256968098459609)
              ·
                refine ⟨13152651018942726073844707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17536868025256968098459609 13152651018942726073844707)
                ·
                  refine ⟨19728976528414089110767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13152651018942726073844707 19728976528414089110767061)
                  ·
                    refine ⟨462397887384705213533603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19728976528414089110767061 462397887384705213533603)
                    ·
                      rfl

theorem cell22_1350775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1350775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350775 prefixEnd_1350775 := by exact prefixLift 1350775
  have htrace : WordTrace (prefixWord ++ tailWord_1350775) baseStart_1350775 baseEnd_1350775 := by
    simpa [prefixWord, tailWord_1350775, baseEnd_1350775] using wordTrace_append hprefix tailTrace_1350775
  have hstable : (prefixWord ++ tailWord_1350775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350775).length < 2 ^ (prefixWord ++ tailWord_1350775).sum := by decide
  have hdescent : baseEnd_1350775 < baseStart_1350775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350781 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_1350781 : Nat := 118140960795 + 1350781 * 2 ^ 59
def prefixEnd_1350781 : Nat := 4983230072969 + 3 ^ 40 * 1350781 * 2
def baseEnd_1350781 : Nat := 462399941307323197883585

theorem tailTrace_1350781 : CollatzResearch.WordTrace tailWord_1350781 prefixEnd_1350781 462399941307323197883585 := by
  unfold tailWord_1350781
  simp only [CollatzResearch.WordTrace]
  refine ⟨49267030519358606873340197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32844687012905737915560131 49267030519358606873340197)
  ·
    refine ⟨9237568222379738788751287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49267030519358606873340197 9237568222379738788751287)
    ·
      refine ⟨13856352333569608183126931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237568222379738788751287 13856352333569608183126931)
      ·
        refine ⟨20784528500354412274690397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856352333569608183126931 20784528500354412274690397)
        ·
          refine ⟨7794198187632904603008899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20784528500354412274690397 7794198187632904603008899)
          ·
            refine ⟨11691297281449356904513349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794198187632904603008899 11691297281449356904513349)
            ·
              refine ⟨2192118240271754419596253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11691297281449356904513349 2192118240271754419596253)
              ·
                refine ⟨822044340101907907348595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2192118240271754419596253 822044340101907907348595)
                ·
                  refine ⟨1233066510152861861022893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822044340101907907348595 1233066510152861861022893)
                  ·
                    refine ⟨462399941307323197883585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233066510152861861022893 462399941307323197883585)
                    ·
                      rfl

theorem cell22_1350781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_1350781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350781 prefixEnd_1350781 := by exact prefixLift 1350781
  have htrace : WordTrace (prefixWord ++ tailWord_1350781) baseStart_1350781 baseEnd_1350781 := by
    simpa [prefixWord, tailWord_1350781, baseEnd_1350781] using wordTrace_append hprefix tailTrace_1350781
  have hstable : (prefixWord ++ tailWord_1350781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350781).length < 2 ^ (prefixWord ++ tailWord_1350781).sum := by decide
  have hdescent : baseEnd_1350781 < baseStart_1350781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350871 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 2, 3]
def baseStart_1350871 : Nat := 118140960795 + 1350871 * 2 ^ 59
def prefixEnd_1350871 : Nat := 4983230072969 + 3 ^ 40 * 1350871 * 2
def baseEnd_1350871 : Nat := 462430750146592963133309

theorem tailTrace_1350871 : CollatzResearch.WordTrace tailWord_1350871 prefixEnd_1350871 462430750146592963133309 := by
  unfold tailWord_1350871
  simp only [CollatzResearch.WordTrace]
  refine ⟨49270313089032552244116467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32846875392688368162744311 49270313089032552244116467)
  ·
    refine ⟨73905469633548828366174701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49270313089032552244116467 73905469633548828366174701)
    ·
      refine ⟨27714551112580810637315513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73905469633548828366174701 27714551112580810637315513)
      ·
        refine ⟨20785913334435607977986635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27714551112580810637315513 20785913334435607977986635)
        ·
          refine ⟨31178870001653411966979953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20785913334435607977986635 31178870001653411966979953)
          ·
            refine ⟨23384152501240058975234965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31178870001653411966979953 23384152501240058975234965)
            ·
              refine ⟨1096132148495627764464139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23384152501240058975234965 1096132148495627764464139)
              ·
                refine ⟨1644198222743441646696209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096132148495627764464139 1644198222743441646696209)
                ·
                  refine ⟨1233148667057581235022157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644198222743441646696209 1233148667057581235022157)
                  ·
                    refine ⟨462430750146592963133309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233148667057581235022157 462430750146592963133309)
                    ·
                      rfl

theorem cell22_1350871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_1350871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1350871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1350871 prefixEnd_1350871 := by exact prefixLift 1350871
  have htrace : WordTrace (prefixWord ++ tailWord_1350871) baseStart_1350871 baseEnd_1350871 := by
    simpa [prefixWord, tailWord_1350871, baseEnd_1350871] using wordTrace_append hprefix tailTrace_1350871
  have hstable : (prefixWord ++ tailWord_1350871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350871).length < 2 ^ (prefixWord ++ tailWord_1350871).sum := by decide
  have hdescent : baseEnd_1350871 < baseStart_1350871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351008 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_1351008 : Nat := 118140960795 + 1351008 * 2 ^ 59
def prefixEnd_1351008 : Nat := 4983230072969 + 3 ^ 40 * 1351008 * 2
def baseEnd_1351008 : Nat := 154159216015456757485963

theorem tailTrace_1351008 : CollatzResearch.WordTrace tailWord_1351008 prefixEnd_1351008 154159216015456757485963 := by
  unfold tailWord_1351008
  simp only [CollatzResearch.WordTrace]
  refine ⟨24637654944768112320926839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32850206593024149761235785 24637654944768112320926839)
  ·
    refine ⟨36956482417152168481390259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24637654944768112320926839 36956482417152168481390259)
    ·
      refine ⟨55434723625728252722085389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36956482417152168481390259 55434723625728252722085389)
      ·
        refine ⟨20788021359648094770782021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55434723625728252722085389 20788021359648094770782021)
        ·
          refine ⟨3897754004934017769521629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20788021359648094770782021 3897754004934017769521629)
          ·
            refine ⟨1461657751850256663570611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3897754004934017769521629 1461657751850256663570611)
            ·
              refine ⟨2192486627775384995355917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461657751850256663570611 2192486627775384995355917)
              ·
                refine ⟨822182485415769373258469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2192486627775384995355917 822182485415769373258469)
                ·
                  refine ⟨154159216015456757485963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822182485415769373258469 154159216015456757485963)
                  ·
                    rfl

theorem cell22_1351008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_1351008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351008 prefixEnd_1351008 := by exact prefixLift 1351008
  have htrace : WordTrace (prefixWord ++ tailWord_1351008) baseStart_1351008 baseEnd_1351008 := by
    simpa [prefixWord, tailWord_1351008, baseEnd_1351008] using wordTrace_append hprefix tailTrace_1351008
  have hstable : (prefixWord ++ tailWord_1351008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351008).length < 2 ^ (prefixWord ++ tailWord_1351008).sum := by decide
  have hdescent : baseEnd_1351008 < baseStart_1351008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351021 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1351021 : Nat := 118140960795 + 1351021 * 2 ^ 59
def prefixEnd_1351021 : Nat := 4983230072969 + 3 ^ 40 * 1351021 * 2
def baseEnd_1351021 : Nat := 462482098212042571882849

theorem tailTrace_1351021 : CollatzResearch.WordTrace tailWord_1351021 prefixEnd_1351021 462482098212042571882849 := by
  unfold tailWord_1351021
  simp only [CollatzResearch.WordTrace]
  refine ⟨49275784038489127862076917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32850522692326085241384611 49275784038489127862076917)
  ·
    refine ⟨4619604753608355737069711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49275784038489127862076917 4619604753608355737069711)
    ·
      refine ⟨6929407130412533605604567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619604753608355737069711 6929407130412533605604567)
      ·
        refine ⟨10394110695618800408406851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929407130412533605604567 10394110695618800408406851)
        ·
          refine ⟨15591166043428200612610277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10394110695618800408406851 15591166043428200612610277)
          ·
            refine ⟨2923343633142787614864427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15591166043428200612610277 2923343633142787614864427)
            ·
              refine ⟨4385015449714181422296641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923343633142787614864427 4385015449714181422296641)
              ·
                refine ⟨3288761587285636066722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4385015449714181422296641 3288761587285636066722481)
                ·
                  refine ⟨2466571190464227050041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288761587285636066722481 2466571190464227050041861)
                  ·
                    refine ⟨462482098212042571882849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466571190464227050041861 462482098212042571882849)
                    ·
                      rfl

theorem cell22_1351021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1351021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351021 prefixEnd_1351021 := by exact prefixLift 1351021
  have htrace : WordTrace (prefixWord ++ tailWord_1351021) baseStart_1351021 baseEnd_1351021 := by
    simpa [prefixWord, tailWord_1351021, baseEnd_1351021] using wordTrace_append hprefix tailTrace_1351021
  have hstable : (prefixWord ++ tailWord_1351021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351021).length < 2 ^ (prefixWord ++ tailWord_1351021).sum := by decide
  have hdescent : baseEnd_1351021 < baseStart_1351021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351106 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1351106 : Nat := 118140960795 + 1351106 * 2 ^ 59
def prefixEnd_1351106 : Nat := 4983230072969 + 3 ^ 40 * 1351106 * 2
def baseEnd_1351106 : Nat := 462511195449130683507589

theorem tailTrace_1351106 : CollatzResearch.WordTrace tailWord_1351106 prefixEnd_1351106 462511195449130683507589 := by
  unfold tailWord_1351106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319721060795296844730293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32852589495454124919280781 12319721060795296844730293)
  ·
    refine ⟨1154973849449559079193465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12319721060795296844730293 1154973849449559079193465)
    ·
      refine ⟨866230387087169309395099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154973849449559079193465 866230387087169309395099)
      ·
        refine ⟨1299345580630753964092649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866230387087169309395099 1299345580630753964092649)
        ·
          refine ⟨974509185473065473069487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299345580630753964092649 974509185473065473069487)
          ·
            refine ⟨1461763778209598209604231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974509185473065473069487 1461763778209598209604231)
            ·
              refine ⟨2192645667314397314406347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461763778209598209604231 2192645667314397314406347)
              ·
                refine ⟨3288968500971595971609521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192645667314397314406347 3288968500971595971609521)
                ·
                  refine ⟨2466726375728696978707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288968500971595971609521 2466726375728696978707141)
                  ·
                    refine ⟨462511195449130683507589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466726375728696978707141 462511195449130683507589)
                    ·
                      rfl

theorem cell22_1351106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1351106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351106 prefixEnd_1351106 := by exact prefixLift 1351106
  have htrace : WordTrace (prefixWord ++ tailWord_1351106) baseStart_1351106 baseEnd_1351106 := by
    simpa [prefixWord, tailWord_1351106, baseEnd_1351106] using wordTrace_append hprefix tailTrace_1351106
  have hstable : (prefixWord ++ tailWord_1351106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351106).length < 2 ^ (prefixWord ++ tailWord_1351106).sum := by decide
  have hdescent : baseEnd_1351106 < baseStart_1351106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351111 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1351111 : Nat := 118140960795 + 1351111 * 2 ^ 59
def prefixEnd_1351111 : Nat := 4983230072969 + 3 ^ 40 * 1351111 * 2
def baseEnd_1351111 : Nat := 462512907051312337132573

theorem tailTrace_1351111 : CollatzResearch.WordTrace tailWord_1351111 prefixEnd_1351111 462512907051312337132573 := by
  unfold tailWord_1351111
  simp only [CollatzResearch.WordTrace]
  refine ⟨49279066608163073232853187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32852711072108715488568791 49279066608163073232853187)
  ·
    refine ⟨73918599912244609849279781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49279066608163073232853187 73918599912244609849279781)
    ·
      refine ⟨13859737483545864346739959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73918599912244609849279781 13859737483545864346739959)
      ·
        refine ⟨20789606225318796520109939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859737483545864346739959 20789606225318796520109939)
        ·
          refine ⟨31184409337978194780164909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20789606225318796520109939 31184409337978194780164909)
          ·
            refine ⟨11694153501741823042561841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31184409337978194780164909 11694153501741823042561841)
            ·
              refine ⟨8770615126306367281921381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694153501741823042561841 8770615126306367281921381)
              ·
                refine ⟨1644490336182443865360259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8770615126306367281921381 1644490336182443865360259)
                ·
                  refine ⟨2466735504273665798040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644490336182443865360259 2466735504273665798040389)
                  ·
                    refine ⟨462512907051312337132573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466735504273665798040389 462512907051312337132573)
                    ·
                      rfl

theorem cell22_1351111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1351111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351111 prefixEnd_1351111 := by exact prefixLift 1351111
  have htrace : WordTrace (prefixWord ++ tailWord_1351111) baseStart_1351111 baseEnd_1351111 := by
    simpa [prefixWord, tailWord_1351111, baseEnd_1351111] using wordTrace_append hprefix tailTrace_1351111
  have hstable : (prefixWord ++ tailWord_1351111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351111).length < 2 ^ (prefixWord ++ tailWord_1351111).sum := by decide
  have hdescent : baseEnd_1351111 < baseStart_1351111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351128 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_1351128 : Nat := 118140960795 + 1351128 * 2 ^ 59
def prefixEnd_1351128 : Nat := 4983230072969 + 3 ^ 40 * 1351128 * 2
def baseEnd_1351128 : Nat := 462518726498729959457521

theorem tailTrace_1351128 : CollatzResearch.WordTrace tailWord_1351128 prefixEnd_1351128 462518726498729959457521 := by
  unfold tailWord_1351128
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639843324550742568111019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32853124432734323424148025 24639843324550742568111019)
  ·
    refine ⟨36959764986826113852166529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24639843324550742568111019 36959764986826113852166529)
    ·
      refine ⟨27719823740119585389124897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36959764986826113852166529 27719823740119585389124897)
      ·
        refine ⟨20789867805089689041843673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27719823740119585389124897 20789867805089689041843673)
        ·
          refine ⟨15592400853817266781382755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20789867805089689041843673 15592400853817266781382755)
          ·
            refine ⟨23388601280725900172074133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15592400853817266781382755 23388601280725900172074133)
            ·
              refine ⟨1096340685034026570565975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23388601280725900172074133 1096340685034026570565975)
              ·
                refine ⟨1644511027551039855848963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096340685034026570565975 1644511027551039855848963)
                ·
                  refine ⟨2466766541326559783773445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644511027551039855848963 2466766541326559783773445)
                  ·
                    refine ⟨462518726498729959457521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466766541326559783773445 462518726498729959457521)
                    ·
                      rfl

theorem cell22_1351128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_1351128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351128 prefixEnd_1351128 := by exact prefixLift 1351128
  have htrace : WordTrace (prefixWord ++ tailWord_1351128) baseStart_1351128 baseEnd_1351128 := by
    simpa [prefixWord, tailWord_1351128, baseEnd_1351128] using wordTrace_append hprefix tailTrace_1351128
  have hstable : (prefixWord ++ tailWord_1351128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351128).length < 2 ^ (prefixWord ++ tailWord_1351128).sum := by decide
  have hdescent : baseEnd_1351128 < baseStart_1351128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351143 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 4]
def baseStart_1351143 : Nat := 118140960795 + 1351143 * 2 ^ 59
def prefixEnd_1351143 : Nat := 4983230072969 + 3 ^ 40 * 1351143 * 2
def baseEnd_1351143 : Nat := 154174620435091640110825

theorem tailTrace_1351143 : CollatzResearch.WordTrace tailWord_1351143 prefixEnd_1351143 154174620435091640110825 := by
  unfold tailWord_1351143
  simp only [CollatzResearch.WordTrace]
  refine ⟨49280233744047142698018083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32853489162698095132012055 49280233744047142698018083)
  ·
    refine ⟨73920350616070714047027125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49280233744047142698018083 73920350616070714047027125)
    ·
      refine ⟨6930032870256629441908793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73920350616070714047027125 6930032870256629441908793)
      ·
        refine ⟨5197524652692472081431595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930032870256629441908793 5197524652692472081431595)
        ·
          refine ⟨7796286979038708122147393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197524652692472081431595 7796286979038708122147393)
          ·
            refine ⟨5847215234279031091610545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7796286979038708122147393 5847215234279031091610545)
            ·
              refine ⟨4385411425709273318707909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5847215234279031091610545 4385411425709273318707909)
              ·
                refine ⟨822264642320488747257733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4385411425709273318707909 822264642320488747257733)
                ·
                  refine ⟨154174620435091640110825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822264642320488747257733 154174620435091640110825)
                  ·
                    rfl

theorem cell22_1351143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 4].length) (baseStart_1351143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351143 prefixEnd_1351143 := by exact prefixLift 1351143
  have htrace : WordTrace (prefixWord ++ tailWord_1351143) baseStart_1351143 baseEnd_1351143 := by
    simpa [prefixWord, tailWord_1351143, baseEnd_1351143] using wordTrace_append hprefix tailTrace_1351143
  have hstable : (prefixWord ++ tailWord_1351143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351143).length < 2 ^ (prefixWord ++ tailWord_1351143).sum := by decide
  have hdescent : baseEnd_1351143 < baseStart_1351143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351158 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1351158 : Nat := 118140960795 + 1351158 * 2 ^ 59
def prefixEnd_1351158 : Nat := 4983230072969 + 3 ^ 40 * 1351158 * 2
def baseEnd_1351158 : Nat := 462528996111819881207429

theorem tailTrace_1351158 : CollatzResearch.WordTrace tailWord_1351158 prefixEnd_1351158 462528996111819881207429 := by
  unfold tailWord_1351158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080048802437050016238383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32853853892661866839876085 3080048802437050016238383)
  ·
    refine ⟨4620073203655575024357575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080048802437050016238383 4620073203655575024357575)
    ·
      refine ⟨6930109805483362536536363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620073203655575024357575 6930109805483362536536363)
      ·
        refine ⟨10395164708225043804804545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930109805483362536536363 10395164708225043804804545)
        ·
          refine ⟨7796373531168782853603409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395164708225043804804545 7796373531168782853603409)
          ·
            refine ⟨5847280148376587140202557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7796373531168782853603409 5847280148376587140202557)
            ·
              refine ⟨2192730055641220177575959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5847280148376587140202557 2192730055641220177575959)
              ·
                refine ⟨3289095083461830266363939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192730055641220177575959 3289095083461830266363939)
                ·
                  refine ⟨4933642625192745399545909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289095083461830266363939 4933642625192745399545909)
                  ·
                    refine ⟨462528996111819881207429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4933642625192745399545909 462528996111819881207429)
                    ·
                      rfl

theorem cell22_1351158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1351158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351158 prefixEnd_1351158 := by exact prefixLift 1351158
  have htrace : WordTrace (prefixWord ++ tailWord_1351158) baseStart_1351158 baseEnd_1351158 := by
    simpa [prefixWord, tailWord_1351158, baseEnd_1351158] using wordTrace_append hprefix tailTrace_1351158
  have hstable : (prefixWord ++ tailWord_1351158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351158).length < 2 ^ (prefixWord ++ tailWord_1351158).sum := by decide
  have hdescent : baseEnd_1351158 < baseStart_1351158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351291 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_1351291 : Nat := 118140960795 + 1351291 * 2 ^ 59
def prefixEnd_1351291 : Nat := 4983230072969 + 3 ^ 40 * 1351291 * 2
def baseEnd_1351291 : Nat := 462574524729851867632021

theorem tailTrace_1351291 : CollatzResearch.WordTrace tailWord_1351291 prefixEnd_1351291 462574524729851867632021 := by
  unfold tailWord_1351291
  simp only [CollatzResearch.WordTrace]
  refine ⟨49285631747510963974405727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32857087831673975982937151 49285631747510963974405727)
  ·
    refine ⟨73928447621266445961608591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49285631747510963974405727 73928447621266445961608591)
    ·
      refine ⟨110892671431899668942412887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73928447621266445961608591 110892671431899668942412887)
      ·
        refine ⟨166339007147849503413619331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110892671431899668942412887 166339007147849503413619331)
        ·
          refine ⟨249508510721774255120428997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166339007147849503413619331 249508510721774255120428997)
          ·
            refine ⟨46782845760332672835080437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249508510721774255120428997 46782845760332672835080437)
            ·
              refine ⟨4385891790031188078288791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46782845760332672835080437 4385891790031188078288791)
              ·
                refine ⟨6578837685046782117433187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385891790031188078288791 6578837685046782117433187)
                ·
                  refine ⟨9868256527570173176149781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578837685046782117433187 9868256527570173176149781)
                  ·
                    refine ⟨462574524729851867632021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9868256527570173176149781 462574524729851867632021)
                    ·
                      rfl

theorem cell22_1351291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_1351291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351291 prefixEnd_1351291 := by exact prefixLift 1351291
  have htrace : WordTrace (prefixWord ++ tailWord_1351291) baseStart_1351291 baseEnd_1351291 := by
    simpa [prefixWord, tailWord_1351291, baseEnd_1351291] using wordTrace_append hprefix tailTrace_1351291
  have hstable : (prefixWord ++ tailWord_1351291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351291).length < 2 ^ (prefixWord ++ tailWord_1351291).sum := by decide
  have hdescent : baseEnd_1351291 < baseStart_1351291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351293 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1351293 : Nat := 118140960795 + 1351293 * 2 ^ 59
def prefixEnd_1351293 : Nat := 4983230072969 + 3 ^ 40 * 1351293 * 2
def baseEnd_1351293 : Nat := 462575209370724529082015

theorem tailTrace_1351293 : CollatzResearch.WordTrace tailWord_1351293 prefixEnd_1351293 462575209370724529082015 := by
  unfold tailWord_1351293
  simp only [CollatzResearch.WordTrace]
  refine ⟨49285704693503718315978533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32857136462335812210652355 49285704693503718315978533)
  ·
    refine ⟨9241069630031947184245975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49285704693503718315978533 9241069630031947184245975)
    ·
      refine ⟨13861604445047920776368963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241069630031947184245975 13861604445047920776368963)
      ·
        refine ⟨20792406667571881164553445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13861604445047920776368963 20792406667571881164553445)
        ·
          refine ⟨3898576250169727718353771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20792406667571881164553445 3898576250169727718353771)
          ·
            refine ⟨5847864375254591577530657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898576250169727718353771 5847864375254591577530657)
            ·
              refine ⟨4385898281440943683147993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5847864375254591577530657 4385898281440943683147993)
              ·
                refine ⟨3289423711080707762360995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4385898281440943683147993 3289423711080707762360995)
                ·
                  refine ⟨4934135566621061643541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289423711080707762360995 4934135566621061643541493)
                  ·
                    refine ⟨462575209370724529082015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4934135566621061643541493 462575209370724529082015)
                    ·
                      rfl

theorem cell22_1351293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1351293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351293 prefixEnd_1351293 := by exact prefixLift 1351293
  have htrace : WordTrace (prefixWord ++ tailWord_1351293) baseStart_1351293 baseEnd_1351293 := by
    simpa [prefixWord, tailWord_1351293, baseEnd_1351293] using wordTrace_append hprefix tailTrace_1351293
  have hstable : (prefixWord ++ tailWord_1351293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351293).length < 2 ^ (prefixWord ++ tailWord_1351293).sum := by decide
  have hdescent : baseEnd_1351293 < baseStart_1351293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351297 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1351297 : Nat := 118140960795 + 1351297 * 2 ^ 59
def prefixEnd_1351297 : Nat := 4983230072969 + 3 ^ 40 * 1351297 * 2
def baseEnd_1351297 : Nat := 462576578652469851982003

theorem tailTrace_1351297 : CollatzResearch.WordTrace tailWord_1351297 prefixEnd_1351297 462576578652469851982003 := by
  unfold tailWord_1351297
  simp only [CollatzResearch.WordTrace]
  refine ⟨49285850585489226999124145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32857233723659484666082763 49285850585489226999124145)
  ·
    refine ⟨36964387939116920249343109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49285850585489226999124145 36964387939116920249343109)
    ·
      refine ⟨6930822738584422546751833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36964387939116920249343109 6930822738584422546751833)
      ·
        refine ⟨5198117053938316910063875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930822738584422546751833 5198117053938316910063875)
        ·
          refine ⟨7797175580907475365095813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198117053938316910063875 7797175580907475365095813)
          ·
            refine ⟨1461970421420151630955465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7797175580907475365095813 1461970421420151630955465)
            ·
              refine ⟨1096477816065113723216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461970421420151630955465 1096477816065113723216599)
              ·
                refine ⟨1644716724097670584824899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096477816065113723216599 1644716724097670584824899)
                ·
                  refine ⟨2467075086146505877237349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644716724097670584824899 2467075086146505877237349)
                  ·
                    refine ⟨462576578652469851982003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2467075086146505877237349 462576578652469851982003)
                    ·
                      rfl

theorem cell22_1351297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1351297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351297 prefixEnd_1351297 := by exact prefixLift 1351297
  have htrace : WordTrace (prefixWord ++ tailWord_1351297) baseStart_1351297 baseEnd_1351297 := by
    simpa [prefixWord, tailWord_1351297, baseEnd_1351297] using wordTrace_append hprefix tailTrace_1351297
  have hstable : (prefixWord ++ tailWord_1351297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351297).length < 2 ^ (prefixWord ++ tailWord_1351297).sum := by decide
  have hdescent : baseEnd_1351297 < baseStart_1351297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351310 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1351310 : Nat := 118140960795 + 1351310 * 2 ^ 59
def prefixEnd_1351310 : Nat := 4983230072969 + 3 ^ 40 * 1351310 * 2
def baseEnd_1351310 : Nat := 462581028818142151406963

theorem tailTrace_1351310 : CollatzResearch.WordTrace tailWord_1351310 prefixEnd_1351310 462581028818142151406963 := by
  unfold tailWord_1351310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160790591805266277418423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32857549822961420146231589 6160790591805266277418423)
  ·
    refine ⟨9241185887707899416127635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160790591805266277418423 9241185887707899416127635)
    ·
      refine ⟨13861778831561849124191453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241185887707899416127635 13861778831561849124191453)
      ·
        refine ⟨5198167061835693421571795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13861778831561849124191453 5198167061835693421571795)
        ·
          refine ⟨7797250592753540132357693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198167061835693421571795 7797250592753540132357693)
          ·
            refine ⟨2923968972282577549634135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7797250592753540132357693 2923968972282577549634135)
            ·
              refine ⟨4385953458423866324451203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923968972282577549634135 4385953458423866324451203)
              ·
                refine ⟨6578930187635799486676805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385953458423866324451203 6578930187635799486676805)
                ·
                  refine ⟨1233549410181712403751901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6578930187635799486676805 1233549410181712403751901)
                  ·
                    refine ⟨462581028818142151406963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233549410181712403751901 462581028818142151406963)
                    ·
                      rfl

theorem cell22_1351310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1351310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351310 prefixEnd_1351310 := by exact prefixLift 1351310
  have htrace : WordTrace (prefixWord ++ tailWord_1351310) baseStart_1351310 baseEnd_1351310 := by
    simpa [prefixWord, tailWord_1351310, baseEnd_1351310] using wordTrace_append hprefix tailTrace_1351310
  have hstable : (prefixWord ++ tailWord_1351310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351310).length < 2 ^ (prefixWord ++ tailWord_1351310).sum := by decide
  have hdescent : baseEnd_1351310 < baseStart_1351310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351327 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 5]
def baseStart_1351327 : Nat := 118140960795 + 1351327 * 2 ^ 59
def prefixEnd_1351327 : Nat := 4983230072969 + 3 ^ 40 * 1351327 * 2
def baseEnd_1351327 : Nat := 462586848265559773731911

theorem tailTrace_1351327 : CollatzResearch.WordTrace tailWord_1351327 prefixEnd_1351327 462586848265559773731911 := by
  unfold tailWord_1351327
  simp only [CollatzResearch.WordTrace]
  refine ⟨49286944775380542122716235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32857963183587028081810823 49286944775380542122716235)
  ·
    refine ⟨73930417163070813184074353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49286944775380542122716235 73930417163070813184074353)
    ·
      refine ⟨55447812872303109888055765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73930417163070813184074353 55447812872303109888055765)
      ·
        refine ⟨1299558114194604138001307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 55447812872303109888055765 1299558114194604138001307)
        ·
          refine ⟨1949337171291906207001961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299558114194604138001307 1949337171291906207001961)
          ·
            refine ⟨1462002878468929655251471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949337171291906207001961 1462002878468929655251471)
            ·
              refine ⟨2193004317703394482877207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462002878468929655251471 2193004317703394482877207)
              ·
                refine ⟨3289506476555091724315811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193004317703394482877207 3289506476555091724315811)
                ·
                  refine ⟨4934259714832637586473717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289506476555091724315811 4934259714832637586473717)
                  ·
                    refine ⟨462586848265559773731911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4934259714832637586473717 462586848265559773731911)
                    ·
                      rfl

theorem cell22_1351327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_1351327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351327 prefixEnd_1351327 := by exact prefixLift 1351327
  have htrace : WordTrace (prefixWord ++ tailWord_1351327) baseStart_1351327 baseEnd_1351327 := by
    simpa [prefixWord, tailWord_1351327, baseEnd_1351327] using wordTrace_append hprefix tailTrace_1351327
  have hstable : (prefixWord ++ tailWord_1351327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351327).length < 2 ^ (prefixWord ++ tailWord_1351327).sum := by decide
  have hdescent : baseEnd_1351327 < baseStart_1351327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351368 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_1351368 : Nat := 118140960795 + 1351368 * 2 ^ 59
def prefixEnd_1351368 : Nat := 4983230072969 + 3 ^ 40 * 1351368 * 2
def baseEnd_1351368 : Nat := 154200294467816444485595

theorem tailTrace_1351368 : CollatzResearch.WordTrace tailWord_1351368 prefixEnd_1351368 154200294467816444485595 := by
  unfold tailWord_1351368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24644220084116003062479379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32858960112154670749972505 24644220084116003062479379)
  ·
    refine ⟨36966330126174004593719069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24644220084116003062479379 36966330126174004593719069)
    ·
      refine ⟨13862373797315251722644651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36966330126174004593719069 13862373797315251722644651)
      ·
        refine ⟨20793560695972877583966977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13862373797315251722644651 20793560695972877583966977)
        ·
          refine ⟨15595170521979658187975233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20793560695972877583966977 15595170521979658187975233)
          ·
            refine ⟨11696377891484743640981425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15595170521979658187975233 11696377891484743640981425)
            ·
              refine ⟨8772283418613557730736069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11696377891484743640981425 8772283418613557730736069)
              ·
                refine ⟨1644803140990042074513013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8772283418613557730736069 1644803140990042074513013)
                ·
                  refine ⟨154200294467816444485595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1644803140990042074513013 154200294467816444485595)
                  ·
                    rfl

theorem cell22_1351368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_1351368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351368 prefixEnd_1351368 := by exact prefixLift 1351368
  have htrace : WordTrace (prefixWord ++ tailWord_1351368) baseStart_1351368 baseEnd_1351368 := by
    simpa [prefixWord, tailWord_1351368, baseEnd_1351368] using wordTrace_append hprefix tailTrace_1351368
  have hstable : (prefixWord ++ tailWord_1351368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351368).length < 2 ^ (prefixWord ++ tailWord_1351368).sum := by decide
  have hdescent : baseEnd_1351368 < baseStart_1351368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351385 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 5]
def baseStart_1351385 : Nat := 118140960795 + 1351385 * 2 ^ 59
def prefixEnd_1351385 : Nat := 4983230072969 + 3 ^ 40 * 1351385 * 2
def baseEnd_1351385 : Nat := 154202234283622318593911

theorem tailTrace_1351385 : CollatzResearch.WordTrace tailWord_1351385 prefixEnd_1351385 154202234283622318593911 := by
  unfold tailWord_1351385
  simp only [CollatzResearch.WordTrace]
  refine ⟨49289060209170418028327609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32859373472780278685551739 49289060209170418028327609)
  ·
    refine ⟨36966795156877813521245707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49289060209170418028327609 36966795156877813521245707)
    ·
      refine ⟨55450192735316720281868561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36966795156877813521245707 55450192735316720281868561)
      ·
        refine ⟨41587644551487540211401421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55450192735316720281868561 41587644551487540211401421)
        ·
          refine ⟨15595366706807827579275533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41587644551487540211401421 15595366706807827579275533)
          ·
            refine ⟨5848262515052935342228325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15595366706807827579275533 5848262515052935342228325)
            ·
              refine ⟨1096549221572425376667811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5848262515052935342228325 1096549221572425376667811)
              ·
                refine ⟨1644823832358638065001717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096549221572425376667811 1644823832358638065001717)
                ·
                  refine ⟨154202234283622318593911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1644823832358638065001717 154202234283622318593911)
                  ·
                    rfl

theorem cell22_1351385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_1351385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351385 prefixEnd_1351385 := by exact prefixLift 1351385
  have htrace : WordTrace (prefixWord ++ tailWord_1351385) baseStart_1351385 baseEnd_1351385 := by
    simpa [prefixWord, tailWord_1351385, baseEnd_1351385] using wordTrace_append hprefix tailTrace_1351385
  have hstable : (prefixWord ++ tailWord_1351385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351385).length < 2 ^ (prefixWord ++ tailWord_1351385).sum := by decide
  have hdescent : baseEnd_1351385 < baseStart_1351385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351445 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1351445 : Nat := 118140960795 + 1351445 * 2 ^ 59
def prefixEnd_1351445 : Nat := 4983230072969 + 3 ^ 40 * 1351445 * 2
def baseEnd_1351445 : Nat := 462627242077046799281549

theorem tailTrace_1351445 : CollatzResearch.WordTrace tailWord_1351445 prefixEnd_1351445 462627242077046799281549 := by
  unfold tailWord_1351445
  simp only [CollatzResearch.WordTrace]
  refine ⟨49291248588953048275511789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32860832392635365517007859 49291248588953048275511789)
  ·
    refine ⟨18484218220857393103316921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49291248588953048275511789 18484218220857393103316921)
    ·
      refine ⟨13863163665643044827487691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18484218220857393103316921 13863163665643044827487691)
      ·
        refine ⟨20794745498464567241231537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13863163665643044827487691 20794745498464567241231537)
        ·
          refine ⟨15596059123848425430923653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794745498464567241231537 15596059123848425430923653)
          ·
            refine ⟨2924261085721579768298185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15596059123848425430923653 2924261085721579768298185)
            ·
              refine ⟨2193195814291184826223639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924261085721579768298185 2193195814291184826223639)
              ·
                refine ⟨3289793721436777239335459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193195814291184826223639 3289793721436777239335459)
                ·
                  refine ⟨4934690582155165859003189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289793721436777239335459 4934690582155165859003189)
                  ·
                    refine ⟨462627242077046799281549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4934690582155165859003189 462627242077046799281549)
                    ·
                      rfl

theorem cell22_1351445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1351445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351445 prefixEnd_1351445 := by exact prefixLift 1351445
  have htrace : WordTrace (prefixWord ++ tailWord_1351445) baseStart_1351445 baseEnd_1351445 := by
    simpa [prefixWord, tailWord_1351445, baseEnd_1351445] using wordTrace_append hprefix tailTrace_1351445
  have hstable : (prefixWord ++ tailWord_1351445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351445).length < 2 ^ (prefixWord ++ tailWord_1351445).sum := by decide
  have hdescent : baseEnd_1351445 < baseStart_1351445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351460 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1351460 : Nat := 118140960795 + 1351460 * 2 ^ 59
def prefixEnd_1351460 : Nat := 4983230072969 + 3 ^ 40 * 1351460 * 2
def baseEnd_1351460 : Nat := 462632376883591760156503

theorem tailTrace_1351460 : CollatzResearch.WordTrace tailWord_1351460 prefixEnd_1351460 462632376883591760156503 := by
  unfold tailWord_1351460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645897841949352918653917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32861197122599137224871889 24645897841949352918653917)
  ·
    refine ⟨9242211690731007344495219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24645897841949352918653917 9242211690731007344495219)
    ·
      refine ⟨13863317536096511016742829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9242211690731007344495219 13863317536096511016742829)
      ·
        refine ⟨5198744076036191631278561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13863317536096511016742829 5198744076036191631278561)
        ·
          refine ⟨3899058057027143723458921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198744076036191631278561 3899058057027143723458921)
          ·
            refine ⟨2924293542770357792594191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899058057027143723458921 2924293542770357792594191)
            ·
              refine ⟨4386440314155536688891287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924293542770357792594191 4386440314155536688891287)
              ·
                refine ⟨6579660471233305033336931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386440314155536688891287 6579660471233305033336931)
                ·
                  refine ⟨9869490706849957550005397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579660471233305033336931 9869490706849957550005397)
                  ·
                    refine ⟨462632376883591760156503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9869490706849957550005397 462632376883591760156503)
                    ·
                      rfl

theorem cell22_1351460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1351460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351460 prefixEnd_1351460 := by exact prefixLift 1351460
  have htrace : WordTrace (prefixWord ++ tailWord_1351460) baseStart_1351460 baseEnd_1351460 := by
    simpa [prefixWord, tailWord_1351460, baseEnd_1351460] using wordTrace_append hprefix tailTrace_1351460
  have hstable : (prefixWord ++ tailWord_1351460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351460).length < 2 ^ (prefixWord ++ tailWord_1351460).sum := by decide
  have hdescent : baseEnd_1351460 < baseStart_1351460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351541 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1351541 : Nat := 118140960795 + 1351541 * 2 ^ 59
def prefixEnd_1351541 : Nat := 4983230072969 + 3 ^ 40 * 1351541 * 2
def baseEnd_1351541 : Nat := 462660104838934548881255

theorem tailTrace_1351541 : CollatzResearch.WordTrace tailWord_1351541 prefixEnd_1351541 462660104838934548881255 := by
  unfold tailWord_1351541
  simp only [CollatzResearch.WordTrace]
  refine ⟨49294749996605256671006477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32863166664403504447337651 49294749996605256671006477)
  ·
    refine ⟨18485531248726971251627429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49294749996605256671006477 18485531248726971251627429)
    ·
      refine ⟨3466037109136307109680143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18485531248726971251627429 3466037109136307109680143)
      ·
        refine ⟨5199055663704460664520215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466037109136307109680143 5199055663704460664520215)
        ·
          refine ⟨7798583495556690996780323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199055663704460664520215 7798583495556690996780323)
          ·
            refine ⟨11697875243335036495170485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7798583495556690996780323 11697875243335036495170485)
            ·
              refine ⟨1096675804062659671422233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11697875243335036495170485 1096675804062659671422233)
              ·
                refine ⟨822506853046994753566675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096675804062659671422233 822506853046994753566675)
                ·
                  refine ⟨1233760279570492130350013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822506853046994753566675 1233760279570492130350013)
                  ·
                    refine ⟨462660104838934548881255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233760279570492130350013 462660104838934548881255)
                    ·
                      rfl

theorem cell22_1351541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1351541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351541 prefixEnd_1351541 := by exact prefixLift 1351541
  have htrace : WordTrace (prefixWord ++ tailWord_1351541) baseStart_1351541 baseEnd_1351541 := by
    simpa [prefixWord, tailWord_1351541, baseEnd_1351541] using wordTrace_append hprefix tailTrace_1351541
  have hstable : (prefixWord ++ tailWord_1351541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351541).length < 2 ^ (prefixWord ++ tailWord_1351541).sum := by decide
  have hdescent : baseEnd_1351541 < baseStart_1351541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351592 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1351592 : Nat := 118140960795 + 1351592 * 2 ^ 59
def prefixEnd_1351592 : Nat := 4983230072969 + 3 ^ 40 * 1351592 * 2
def baseEnd_1351592 : Nat := 462677563181187415856099

theorem tailTrace_1351592 : CollatzResearch.WordTrace tailWord_1351592 prefixEnd_1351592 462677563181187415856099 := by
  unfold tailWord_1351592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24648305059710246190556515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32864406746280328254075353 24648305059710246190556515)
  ·
    refine ⟨36972457589565369285834773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24648305059710246190556515 36972457589565369285834773)
    ·
      refine ⟨1733083949510876685273505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36972457589565369285834773 1733083949510876685273505)
      ·
        refine ⟨1299812962133157513955129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733083949510876685273505 1299812962133157513955129)
        ·
          refine ⟨974859721599868135466347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299812962133157513955129 974859721599868135466347)
          ·
            refine ⟨1462289582399802203199521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974859721599868135466347 1462289582399802203199521)
            ·
              refine ⟨1096717186799851652399641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462289582399802203199521 1096717186799851652399641)
              ·
                refine ⟨822537890099888739299731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096717186799851652399641 822537890099888739299731)
                ·
                  refine ⟨1233806835149833108949597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822537890099888739299731 1233806835149833108949597)
                  ·
                    refine ⟨462677563181187415856099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233806835149833108949597 462677563181187415856099)
                    ·
                      rfl

theorem cell22_1351592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1351592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351592 prefixEnd_1351592 := by exact prefixLift 1351592
  have htrace : WordTrace (prefixWord ++ tailWord_1351592) baseStart_1351592 baseEnd_1351592 := by
    simpa [prefixWord, tailWord_1351592, baseEnd_1351592] using wordTrace_append hprefix tailTrace_1351592
  have hstable : (prefixWord ++ tailWord_1351592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351592).length < 2 ^ (prefixWord ++ tailWord_1351592).sum := by decide
  have hdescent : baseEnd_1351592 < baseStart_1351592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351614 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1351614 : Nat := 118140960795 + 1351614 * 2 ^ 59
def prefixEnd_1351614 : Nat := 4983230072969 + 3 ^ 40 * 1351614 * 2
def baseEnd_1351614 : Nat := 462685094230786691806031

theorem tailTrace_1351614 : CollatzResearch.WordTrace tailWord_1351614 prefixEnd_1351614 462685094230786691806031 := by
  unfold tailWord_1351614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162176565667598767301737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32864941683560526758942597 6162176565667598767301737)
  ·
    refine ⟨4621632424250699075476303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6162176565667598767301737 4621632424250699075476303)
    ·
      refine ⟨6932448636376048613214455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621632424250699075476303 6932448636376048613214455)
      ·
        refine ⟨10398672954564072919821683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6932448636376048613214455 10398672954564072919821683)
        ·
          refine ⟨15598009431846109379732525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398672954564072919821683 15598009431846109379732525)
          ·
            refine ⟨5849253536942291017399697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15598009431846109379732525 5849253536942291017399697)
            ·
              refine ⟨4386940152706718263049773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849253536942291017399697 4386940152706718263049773)
              ·
                refine ⟨1645102557265019348643665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4386940152706718263049773 1645102557265019348643665)
                ·
                  refine ⟨1233826917948764511482749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645102557265019348643665 1233826917948764511482749)
                  ·
                    refine ⟨462685094230786691806031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233826917948764511482749 462685094230786691806031)
                    ·
                      rfl

theorem cell22_1351614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1351614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351614 prefixEnd_1351614 := by exact prefixLift 1351614
  have htrace : WordTrace (prefixWord ++ tailWord_1351614) baseStart_1351614 baseEnd_1351614 := by
    simpa [prefixWord, tailWord_1351614, baseEnd_1351614] using wordTrace_append hprefix tailTrace_1351614
  have hstable : (prefixWord ++ tailWord_1351614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351614).length < 2 ^ (prefixWord ++ tailWord_1351614).sum := by decide
  have hdescent : baseEnd_1351614 < baseStart_1351614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351717 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1351717 : Nat := 118140960795 + 1351717 * 2 ^ 59
def prefixEnd_1351717 : Nat := 4983230072969 + 3 ^ 40 * 1351717 * 2
def baseEnd_1351717 : Nat := 154240117745242918826905

theorem tailTrace_1351717 : CollatzResearch.WordTrace tailWord_1351717 prefixEnd_1351717 154240117745242918826905 := by
  unfold tailWord_1351717
  simp only [CollatzResearch.WordTrace]
  refine ⟨49301169243967638729413405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32867446162645092486275603 49301169243967638729413405)
  ·
    refine ⟨18487938466487864523530027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49301169243967638729413405 18487938466487864523530027)
    ·
      refine ⟨27731907699731796785295041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18487938466487864523530027 27731907699731796785295041)
      ·
        refine ⟨20798930774798847588971281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27731907699731796785295041 20798930774798847588971281)
        ·
          refine ⟨15599198081099135691728461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798930774798847588971281 15599198081099135691728461)
          ·
            refine ⟨5849699280412175884398173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15599198081099135691728461 5849699280412175884398173)
            ·
              refine ⟨2193637230154565956649315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5849699280412175884398173 2193637230154565956649315)
              ·
                refine ⟨3290455845231848934973973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193637230154565956649315 3290455845231848934973973)
                ·
                  refine ⟨154240117745242918826905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3290455845231848934973973 154240117745242918826905)
                  ·
                    rfl

theorem cell22_1351717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1351717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351717 prefixEnd_1351717 := by exact prefixLift 1351717
  have htrace : WordTrace (prefixWord ++ tailWord_1351717) baseStart_1351717 baseEnd_1351717 := by
    simpa [prefixWord, tailWord_1351717, baseEnd_1351717] using wordTrace_append hprefix tailTrace_1351717
  have hstable : (prefixWord ++ tailWord_1351717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351717).length < 2 ^ (prefixWord ++ tailWord_1351717).sum := by decide
  have hdescent : baseEnd_1351717 < baseStart_1351717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351736 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1351736 : Nat := 118140960795 + 1351736 * 2 ^ 59
def prefixEnd_1351736 : Nat := 4983230072969 + 3 ^ 40 * 1351736 * 2
def baseEnd_1351736 : Nat := 462726857324019040255657

theorem tailTrace_1351736 : CollatzResearch.WordTrace tailWord_1351736 prefixEnd_1351736 462726857324019040255657 := by
  unfold tailWord_1351736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650931115449402487177531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32867908153932536649570041 24650931115449402487177531)
  ·
    refine ⟨36976396673174103730766297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650931115449402487177531 36976396673174103730766297)
    ·
      refine ⟨27732297504880577798074723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36976396673174103730766297 27732297504880577798074723)
      ·
        refine ⟨41598446257320866697112085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27732297504880577798074723 41598446257320866697112085)
        ·
          refine ⟨1949927168311915626427129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41598446257320866697112085 1949927168311915626427129)
          ·
            refine ⟨1462445376233936719820347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949927168311915626427129 1462445376233936719820347)
            ·
              refine ⟨2193668064350905079730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462445376233936719820347 2193668064350905079730521)
              ·
                refine ⟨1645251048263178809797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193668064350905079730521 1645251048263178809797891)
                ·
                  refine ⟨2467876572394768214696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645251048263178809797891 2467876572394768214696837)
                  ·
                    refine ⟨462726857324019040255657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2467876572394768214696837 462726857324019040255657)
                    ·
                      rfl

theorem cell22_1351736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1351736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351736 prefixEnd_1351736 := by exact prefixLift 1351736
  have htrace : WordTrace (prefixWord ++ tailWord_1351736) baseStart_1351736 baseEnd_1351736 := by
    simpa [prefixWord, tailWord_1351736, baseEnd_1351736] using wordTrace_append hprefix tailTrace_1351736
  have hstable : (prefixWord ++ tailWord_1351736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351736).length < 2 ^ (prefixWord ++ tailWord_1351736).sum := by decide
  have hdescent : baseEnd_1351736 < baseStart_1351736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351762 : List Nat := [3, 2, 2, 1, 4, 10]
def baseStart_1351762 : Nat := 118140960795 + 1351762 * 2 ^ 59
def prefixEnd_1351762 : Nat := 4983230072969 + 3 ^ 40 * 1351762 * 2
def baseEnd_1351762 : Nat := 5712787131547699248217

theorem tailTrace_1351762 : CollatzResearch.WordTrace tailWord_1351762 prefixEnd_1351762 5712787131547699248217 := by
  unfold tailWord_1351762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325702632201152853700385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32868540352536407609867693 12325702632201152853700385)
  ·
    refine ⟨9244276974150864640275289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12325702632201152853700385 9244276974150864640275289)
    ·
      refine ⟨6933207730613148480206467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9244276974150864640275289 6933207730613148480206467)
      ·
        refine ⟨10399811595919722720309701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6933207730613148480206467 10399811595919722720309701)
        ·
          refine ⟨1949964674234948010058069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10399811595919722720309701 1949964674234948010058069)
          ·
            refine ⟨5712787131547699248217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1949964674234948010058069 5712787131547699248217)
            ·
              rfl

theorem cell22_1351762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 10].length) (baseStart_1351762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351762 prefixEnd_1351762 := by exact prefixLift 1351762
  have htrace : WordTrace (prefixWord ++ tailWord_1351762) baseStart_1351762 baseEnd_1351762 := by
    simpa [prefixWord, tailWord_1351762, baseEnd_1351762] using wordTrace_append hprefix tailTrace_1351762
  have hstable : (prefixWord ++ tailWord_1351762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351762).length < 2 ^ (prefixWord ++ tailWord_1351762).sum := by decide
  have hdescent : baseEnd_1351762 < baseStart_1351762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351794 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1351794 : Nat := 118140960795 + 1351794 * 2 ^ 59
def prefixEnd_1351794 : Nat := 4983230072969 + 3 ^ 40 * 1351794 * 2
def baseEnd_1351794 : Nat := 462746711909326222305479

theorem tailTrace_1351794 : CollatzResearch.WordTrace tailWord_1351794 prefixEnd_1351794 462746711909326222305479 := by
  unfold tailWord_1351794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325994416172170219991609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32869318443125787253310957 12325994416172170219991609)
  ·
    refine ⟨9244495812129127664993707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12325994416172170219991609 9244495812129127664993707)
    ·
      refine ⟨13866743718193691497490561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9244495812129127664993707 13866743718193691497490561)
      ·
        refine ⟨10400057788645268623117921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13866743718193691497490561 10400057788645268623117921)
        ·
          refine ⟨7800043341483951467338441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10400057788645268623117921 7800043341483951467338441)
          ·
            refine ⟨5850032506112963600503831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7800043341483951467338441 5850032506112963600503831)
            ·
              refine ⟨8775048759169445400755747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850032506112963600503831 8775048759169445400755747)
              ·
                refine ⟨13162573138754168101133621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8775048759169445400755747 13162573138754168101133621)
                ·
                  refine ⟨1233991231758203259481277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13162573138754168101133621 1233991231758203259481277)
                  ·
                    refine ⟨462746711909326222305479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233991231758203259481277 462746711909326222305479)
                    ·
                      rfl

theorem cell22_1351794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1351794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351794 prefixEnd_1351794 := by exact prefixLift 1351794
  have htrace : WordTrace (prefixWord ++ tailWord_1351794) baseStart_1351794 baseEnd_1351794 := by
    simpa [prefixWord, tailWord_1351794, baseEnd_1351794] using wordTrace_append hprefix tailTrace_1351794
  have hstable : (prefixWord ++ tailWord_1351794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351794).length < 2 ^ (prefixWord ++ tailWord_1351794).sum := by decide
  have hdescent : baseEnd_1351794 < baseStart_1351794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351811 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 1, 3]
def baseStart_1351811 : Nat := 118140960795 + 1351811 * 2 ^ 59
def prefixEnd_1351811 : Nat := 4983230072969 + 3 ^ 40 * 1351811 * 2
def baseEnd_1351811 : Nat := 462752531356743844630427

theorem tailTrace_1351811 : CollatzResearch.WordTrace tailWord_1351811 prefixEnd_1351811 462752531356743844630427 := by
  unfold tailWord_1351811
  simp only [CollatzResearch.WordTrace]
  refine ⟨49304597705627092783335287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32869731803751395188890191 49304597705627092783335287)
  ·
    refine ⟨73956896558440639175002931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49304597705627092783335287 73956896558440639175002931)
    ·
      refine ⟨110935344837660958762504397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73956896558440639175002931 110935344837660958762504397)
      ·
        refine ⟨41600754314122859535939149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110935344837660958762504397 41600754314122859535939149)
        ·
          refine ⟨15600282867796072325977181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41600754314122859535939149 15600282867796072325977181)
          ·
            refine ⟨5850106075423527122241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15600282867796072325977181 5850106075423527122241443)
            ·
              refine ⟨8775159113135290683362165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850106075423527122241443 8775159113135290683362165)
              ·
                refine ⟨822671166856433501565203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8775159113135290683362165 822671166856433501565203)
                ·
                  refine ⟨1234006750284650252347805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822671166856433501565203 1234006750284650252347805)
                  ·
                    refine ⟨462752531356743844630427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234006750284650252347805 462752531356743844630427)
                    ·
                      rfl

theorem cell22_1351811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 3].length) (baseStart_1351811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351811 prefixEnd_1351811 := by exact prefixLift 1351811
  have htrace : WordTrace (prefixWord ++ tailWord_1351811) baseStart_1351811 baseEnd_1351811 := by
    simpa [prefixWord, tailWord_1351811, baseEnd_1351811] using wordTrace_append hprefix tailTrace_1351811
  have hstable : (prefixWord ++ tailWord_1351811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351811).length < 2 ^ (prefixWord ++ tailWord_1351811).sum := by decide
  have hdescent : baseEnd_1351811 < baseStart_1351811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351839 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_1351839 : Nat := 118140960795 + 1351839 * 2 ^ 59
def prefixEnd_1351839 : Nat := 4983230072969 + 3 ^ 40 * 1351839 * 2
def baseEnd_1351839 : Nat := 462762116328961104930341

theorem tailTrace_1351839 : CollatzResearch.WordTrace tailWord_1351839 prefixEnd_1351839 462762116328961104930341 := by
  unfold tailWord_1351839
  simp only [CollatzResearch.WordTrace]
  refine ⟨49305618949525653565354571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32870412633017102376903047 49305618949525653565354571)
  ·
    refine ⟨73958428424288480348031857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49305618949525653565354571 73958428424288480348031857)
    ·
      refine ⟨55468821318216360261023893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73958428424288480348031857 55468821318216360261023893)
      ·
        refine ⟨2600100999291391887235495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55468821318216360261023893 2600100999291391887235495)
        ·
          refine ⟨3900151498937087830853243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600100999291391887235495 3900151498937087830853243)
          ·
            refine ⟨5850227248405631746279865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900151498937087830853243 5850227248405631746279865)
            ·
              refine ⟨4387670436304223809709899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5850227248405631746279865 4387670436304223809709899)
              ·
                refine ⟨6581505654456335714564849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387670436304223809709899 6581505654456335714564849)
                ·
                  refine ⟨4936129240842251785923637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581505654456335714564849 4936129240842251785923637)
                  ·
                    refine ⟨462762116328961104930341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4936129240842251785923637 462762116328961104930341)
                    ·
                      rfl

theorem cell22_1351839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_1351839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351839 prefixEnd_1351839 := by exact prefixLift 1351839
  have htrace : WordTrace (prefixWord ++ tailWord_1351839) baseStart_1351839 baseEnd_1351839 := by
    simpa [prefixWord, tailWord_1351839, baseEnd_1351839] using wordTrace_append hprefix tailTrace_1351839
  have hstable : (prefixWord ++ tailWord_1351839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351839).length < 2 ^ (prefixWord ++ tailWord_1351839).sum := by decide
  have hdescent : baseEnd_1351839 < baseStart_1351839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351841 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 5]
def baseStart_1351841 : Nat := 118140960795 + 1351841 * 2 ^ 59
def prefixEnd_1351841 : Nat := 4983230072969 + 3 ^ 40 * 1351841 * 2
def baseEnd_1351841 : Nat := 154254266989944588793445

theorem tailTrace_1351841 : CollatzResearch.WordTrace tailWord_1351841 prefixEnd_1351841 154254266989944588793445 := by
  unfold tailWord_1351841
  simp only [CollatzResearch.WordTrace]
  refine ⟨49305691895518407906927377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32870461263678938604618251 49305691895518407906927377)
  ·
    refine ⟨36979268921638805930195533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49305691895518407906927377 36979268921638805930195533)
    ·
      refine ⟨13867225845614552223823325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36979268921638805930195533 13867225845614552223823325)
      ·
        refine ⟨5200209692105457083933747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13867225845614552223823325 5200209692105457083933747)
        ·
          refine ⟨7800314538158185625900621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200209692105457083933747 7800314538158185625900621)
          ·
            refine ⟨2925117951809319609712733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7800314538158185625900621 2925117951809319609712733)
            ·
              refine ⟨1096919231928494853642275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2925117951809319609712733 1096919231928494853642275)
              ·
                refine ⟨1645378847892742280463413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096919231928494853642275 1645378847892742280463413)
                ·
                  refine ⟨154254266989944588793445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645378847892742280463413 154254266989944588793445)
                  ·
                    rfl

theorem cell22_1351841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_1351841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351841 prefixEnd_1351841 := by exact prefixLift 1351841
  have htrace : WordTrace (prefixWord ++ tailWord_1351841) baseStart_1351841 baseEnd_1351841 := by
    simpa [prefixWord, tailWord_1351841, baseEnd_1351841] using wordTrace_append hprefix tailTrace_1351841
  have hstable : (prefixWord ++ tailWord_1351841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351841).length < 2 ^ (prefixWord ++ tailWord_1351841).sum := by decide
  have hdescent : baseEnd_1351841 < baseStart_1351841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351867 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_1351867 : Nat := 118140960795 + 1351867 * 2 ^ 59
def prefixEnd_1351867 : Nat := 4983230072969 + 3 ^ 40 * 1351867 * 2
def baseEnd_1351867 : Nat := 462771701301178365230255

theorem tailTrace_1351867 : CollatzResearch.WordTrace tailWord_1351867 prefixEnd_1351867 462771701301178365230255 := by
  unfold tailWord_1351867
  simp only [CollatzResearch.WordTrace]
  refine ⟨49306640193424214347373855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32871093462282809564915903 49306640193424214347373855)
  ·
    refine ⟨73959960290136321521060783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49306640193424214347373855 73959960290136321521060783)
    ·
      refine ⟨110939940435204482281591175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73959960290136321521060783 110939940435204482281591175)
      ·
        refine ⟨166409910652806723422386763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110939940435204482281591175 166409910652806723422386763)
        ·
          refine ⟨249614865979210085133580145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166409910652806723422386763 249614865979210085133580145)
          ·
            refine ⟨187211149484407563850185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249614865979210085133580145 187211149484407563850185109)
            ·
              refine ⟨8775522632081604555477427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187211149484407563850185109 8775522632081604555477427)
              ·
                refine ⟨13163283948122406833216141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8775522632081604555477427 13163283948122406833216141)
                ·
                  refine ⟨4936231480545902562456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13163283948122406833216141 4936231480545902562456053)
                  ·
                    refine ⟨462771701301178365230255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4936231480545902562456053 462771701301178365230255)
                    ·
                      rfl

theorem cell22_1351867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_1351867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351867 prefixEnd_1351867 := by exact prefixLift 1351867
  have htrace : WordTrace (prefixWord ++ tailWord_1351867) baseStart_1351867 baseEnd_1351867 := by
    simpa [prefixWord, tailWord_1351867, baseEnd_1351867] using wordTrace_append hprefix tailTrace_1351867
  have hstable : (prefixWord ++ tailWord_1351867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351867).length < 2 ^ (prefixWord ++ tailWord_1351867).sum := by decide
  have hdescent : baseEnd_1351867 < baseStart_1351867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351886 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1351886 : Nat := 118140960795 + 1351886 * 2 ^ 59
def prefixEnd_1351886 : Nat := 4983230072969 + 3 ^ 40 * 1351886 * 2
def baseEnd_1351886 : Nat := 154259401796489549668399

theorem tailTrace_1351886 : CollatzResearch.WordTrace tailWord_1351886 prefixEnd_1351886 154259401796489549668399 := by
  unfold tailWord_1351886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163416647544422574039439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32871555453570253728210341 6163416647544422574039439)
  ·
    refine ⟨9245124971316633861059159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6163416647544422574039439 9245124971316633861059159)
    ·
      refine ⟨13867687456974950791588739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9245124971316633861059159 13867687456974950791588739)
      ·
        refine ⟨20801531185462426187383109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867687456974950791588739 20801531185462426187383109)
        ·
          refine ⟨3900287097274204910134333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20801531185462426187383109 3900287097274204910134333)
          ·
            refine ⟨1462607661477826841300375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3900287097274204910134333 1462607661477826841300375)
            ·
              refine ⟨2193911492216740261950563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462607661477826841300375 2193911492216740261950563)
              ·
                refine ⟨3290867238325110392925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193911492216740261950563 3290867238325110392925845)
                ·
                  refine ⟨154259401796489549668399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3290867238325110392925845 154259401796489549668399)
                  ·
                    rfl

theorem cell22_1351886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1351886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351886 prefixEnd_1351886 := by exact prefixLift 1351886
  have htrace : WordTrace (prefixWord ++ tailWord_1351886) baseStart_1351886 baseEnd_1351886 := by
    simpa [prefixWord, tailWord_1351886, baseEnd_1351886] using wordTrace_append hprefix tailTrace_1351886
  have hstable : (prefixWord ++ tailWord_1351886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351886).length < 2 ^ (prefixWord ++ tailWord_1351886).sum := by decide
  have hdescent : baseEnd_1351886 < baseStart_1351886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351897 : List Nat := [1, 2, 1, 2, 3, 1, 3, 9]
def baseStart_1351897 : Nat := 118140960795 + 1351897 * 2 ^ 59
def prefixEnd_1351897 : Nat := 4983230072969 + 3 ^ 40 * 1351897 * 2
def baseEnd_1351897 : Nat := 51420218990474254108907

theorem tailTrace_1351897 : CollatzResearch.WordTrace tailWord_1351897 prefixEnd_1351897 51420218990474254108907 := by
  unfold tailWord_1351897
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307734383315529470965945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32871822922210352980643963 49307734383315529470965945)
  ·
    refine ⟨36980800787486647103224459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49307734383315529470965945 36980800787486647103224459)
    ·
      refine ⟨55471201181229970654836689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36980800787486647103224459 55471201181229970654836689)
      ·
        refine ⟨41603400885922477991127517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55471201181229970654836689 41603400885922477991127517)
        ·
          refine ⟨15601275332220929246672819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41603400885922477991127517 15601275332220929246672819)
          ·
            refine ⟨23401912998331393870009229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601275332220929246672819 23401912998331393870009229)
            ·
              refine ⟨8775717374374272701253461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23401912998331393870009229 8775717374374272701253461)
              ·
                refine ⟨51420218990474254108907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8775717374374272701253461 51420218990474254108907)
                ·
                  rfl

theorem cell22_1351897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 9].length) (baseStart_1351897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351897 prefixEnd_1351897 := by exact prefixLift 1351897
  have htrace : WordTrace (prefixWord ++ tailWord_1351897) baseStart_1351897 baseEnd_1351897 := by
    simpa [prefixWord, tailWord_1351897, baseEnd_1351897] using wordTrace_append hprefix tailTrace_1351897
  have hstable : (prefixWord ++ tailWord_1351897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351897).length < 2 ^ (prefixWord ++ tailWord_1351897).sum := by decide
  have hdescent : baseEnd_1351897 < baseStart_1351897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351927 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1351927 : Nat := 118140960795 + 1351927 * 2 ^ 59
def prefixEnd_1351927 : Nat := 4983230072969 + 3 ^ 40 * 1351927 * 2
def baseEnd_1351927 : Nat := 462792240527358208730071

theorem tailTrace_1351927 : CollatzResearch.WordTrace tailWord_1351927 prefixEnd_1351927 462792240527358208730071 := by
  unfold tailWord_1351927
  simp only [CollatzResearch.WordTrace]
  refine ⟨49308828573206844594558035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32872552382137896396372023 49308828573206844594558035)
  ·
    refine ⟨73963242859810266891837053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49308828573206844594558035 73963242859810266891837053)
    ·
      refine ⟨27736216072428850084438895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73963242859810266891837053 27736216072428850084438895)
      ·
        refine ⟨41604324108643275126658343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27736216072428850084438895 41604324108643275126658343)
        ·
          refine ⟨62406486162964912689987515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41604324108643275126658343 62406486162964912689987515)
          ·
            refine ⟨93609729244447369034981273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62406486162964912689987515 93609729244447369034981273)
            ·
              refine ⟨70207296933335526776235955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93609729244447369034981273 70207296933335526776235955)
              ·
                refine ⟨105310945400003290164353933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70207296933335526776235955 105310945400003290164353933)
                ·
                  refine ⟨39491604525001233811632725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105310945400003290164353933 39491604525001233811632725)
                  ·
                    refine ⟨462792240527358208730071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39491604525001233811632725 462792240527358208730071)
                    ·
                      rfl

theorem cell22_1351927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1351927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351927 prefixEnd_1351927 := by exact prefixLift 1351927
  have htrace : WordTrace (prefixWord ++ tailWord_1351927) baseStart_1351927 baseEnd_1351927 := by
    simpa [prefixWord, tailWord_1351927, baseEnd_1351927] using wordTrace_append hprefix tailTrace_1351927
  have hstable : (prefixWord ++ tailWord_1351927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351927).length < 2 ^ (prefixWord ++ tailWord_1351927).sum := by decide
  have hdescent : baseEnd_1351927 < baseStart_1351927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351929 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_1351929 : Nat := 118140960795 + 1351929 * 2 ^ 59
def prefixEnd_1351929 : Nat := 4983230072969 + 3 ^ 40 * 1351929 * 2
def baseEnd_1351929 : Nat := 462792925168230870180065

theorem tailTrace_1351929 : CollatzResearch.WordTrace tailWord_1351929 prefixEnd_1351929 462792925168230870180065 := by
  unfold tailWord_1351929
  simp only [CollatzResearch.WordTrace]
  refine ⟨49308901519199598936130841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32872601012799732624087227 49308901519199598936130841)
  ·
    refine ⟨36981676139399699202098131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49308901519199598936130841 36981676139399699202098131)
    ·
      refine ⟨55472514209099548803147197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36981676139399699202098131 55472514209099548803147197)
      ·
        refine ⟨20802192828412330801180199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55472514209099548803147197 20802192828412330801180199)
        ·
          refine ⟨31203289242618496201770299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20802192828412330801180199 31203289242618496201770299)
          ·
            refine ⟨46804933863927744302655449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31203289242618496201770299 46804933863927744302655449)
            ·
              refine ⟨35103700397945808226991587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46804933863927744302655449 35103700397945808226991587)
              ·
                refine ⟨52655550596918712340487381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35103700397945808226991587 52655550596918712340487381)
                ·
                  refine ⟨1234114467115282320480173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52655550596918712340487381 1234114467115282320480173)
                  ·
                    refine ⟨462792925168230870180065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234114467115282320480173 462792925168230870180065)
                    ·
                      rfl

theorem cell22_1351929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_1351929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351929 prefixEnd_1351929 := by exact prefixLift 1351929
  have htrace : WordTrace (prefixWord ++ tailWord_1351929) baseStart_1351929 baseEnd_1351929 := by
    simpa [prefixWord, tailWord_1351929, baseEnd_1351929] using wordTrace_append hprefix tailTrace_1351929
  have hstable : (prefixWord ++ tailWord_1351929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351929).length < 2 ^ (prefixWord ++ tailWord_1351929).sum := by decide
  have hdescent : baseEnd_1351929 < baseStart_1351929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351944 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1351944 : Nat := 118140960795 + 1351944 * 2 ^ 59
def prefixEnd_1351944 : Nat := 4983230072969 + 3 ^ 40 * 1351944 * 2
def baseEnd_1351944 : Nat := 462798059974775831055019

theorem tailTrace_1351944 : CollatzResearch.WordTrace tailWord_1351944 prefixEnd_1351944 462798059974775831055019 := by
  unfold tailWord_1351944
  simp only [CollatzResearch.WordTrace]
  refine ⟨24654724307072628248963443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32872965742763504331951257 24654724307072628248963443)
  ·
    refine ⟨36982086460608942373445165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24654724307072628248963443 36982086460608942373445165)
    ·
      refine ⟨13868282422728353390041937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36982086460608942373445165 13868282422728353390041937)
      ·
        refine ⟨10401211817046265042531453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13868282422728353390041937 10401211817046265042531453)
        ·
          refine ⟨3900454431392349390949295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10401211817046265042531453 3900454431392349390949295)
          ·
            refine ⟨5850681647088524086423943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900454431392349390949295 5850681647088524086423943)
            ·
              refine ⟨8776022470632786129635915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850681647088524086423943 8776022470632786129635915)
              ·
                refine ⟨13164033705949179194453873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776022470632786129635915 13164033705949179194453873)
                ·
                  refine ⟨9873025279461884395840405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13164033705949179194453873 9873025279461884395840405)
                  ·
                    refine ⟨462798059974775831055019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9873025279461884395840405 462798059974775831055019)
                    ·
                      rfl

theorem cell22_1351944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1351944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351944 prefixEnd_1351944 := by exact prefixLift 1351944
  have htrace : WordTrace (prefixWord ++ tailWord_1351944) baseStart_1351944 baseEnd_1351944 := by
    simpa [prefixWord, tailWord_1351944, baseEnd_1351944] using wordTrace_append hprefix tailTrace_1351944
  have hstable : (prefixWord ++ tailWord_1351944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351944).length < 2 ^ (prefixWord ++ tailWord_1351944).sum := by decide
  have hdescent : baseEnd_1351944 < baseStart_1351944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351993 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 5]
def baseStart_1351993 : Nat := 118140960795 + 1351993 * 2 ^ 59
def prefixEnd_1351993 : Nat := 4983230072969 + 3 ^ 40 * 1351993 * 2
def baseEnd_1351993 : Nat := 154271611225385345526623

theorem tailTrace_1351993 : CollatzResearch.WordTrace tailWord_1351993 prefixEnd_1351993 154271611225385345526623 := by
  unfold tailWord_1351993
  simp only [CollatzResearch.WordTrace]
  refine ⟨49311235790967737866460633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32874157193978491910973755 49311235790967737866460633)
  ·
    refine ⟨36983426843225803399845475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49311235790967737866460633 36983426843225803399845475)
    ·
      refine ⟨55475140264838705099768213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36983426843225803399845475 55475140264838705099768213)
      ·
        refine ⟨2600397199914314301551635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55475140264838705099768213 2600397199914314301551635)
        ·
          refine ⟨3900595799871471452327453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600397199914314301551635 3900595799871471452327453)
          ·
            refine ⟨1462723424951801794622795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3900595799871471452327453 1462723424951801794622795)
            ·
              refine ⟨2194085137427702691934193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462723424951801794622795 2194085137427702691934193)
              ·
                refine ⟨1645563853070777018950645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194085137427702691934193 1645563853070777018950645)
                ·
                  refine ⟨154271611225385345526623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645563853070777018950645 154271611225385345526623)
                  ·
                    rfl

theorem cell22_1351993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_1351993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1351993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1351993 prefixEnd_1351993 := by exact prefixLift 1351993
  have htrace : WordTrace (prefixWord ++ tailWord_1351993) baseStart_1351993 baseEnd_1351993 := by
    simpa [prefixWord, tailWord_1351993, baseEnd_1351993] using wordTrace_append hprefix tailTrace_1351993
  have hstable : (prefixWord ++ tailWord_1351993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351993).length < 2 ^ (prefixWord ++ tailWord_1351993).sum := by decide
  have hdescent : baseEnd_1351993 < baseStart_1351993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352019 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_1352019 : Nat := 118140960795 + 1352019 * 2 ^ 59
def prefixEnd_1352019 : Nat := 4983230072969 + 3 ^ 40 * 1352019 * 2
def baseEnd_1352019 : Nat := 462823734007500635429789

theorem tailTrace_1352019 : CollatzResearch.WordTrace tailWord_1352019 prefixEnd_1352019 462823734007500635429789 := by
  unfold tailWord_1352019
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312184088873544306907111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32874789392582362871271407 49312184088873544306907111)
  ·
    refine ⟨73968276133310316460360667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49312184088873544306907111 73968276133310316460360667)
    ·
      refine ⟨110952414199965474690541001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73968276133310316460360667 110952414199965474690541001)
      ·
        refine ⟨83214310649974106017905751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110952414199965474690541001 83214310649974106017905751)
        ·
          refine ⟨124821465974961159026858627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83214310649974106017905751 124821465974961159026858627)
          ·
            refine ⟨187232198962441738540287941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124821465974961159026858627 187232198962441738540287941)
            ·
              refine ⟨35106037305457825976303989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187232198962441738540287941 35106037305457825976303989)
              ·
                refine ⟨3291190997386671185278499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35106037305457825976303989 3291190997386671185278499)
                ·
                  refine ⟨4936786496080006777917749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291190997386671185278499 4936786496080006777917749)
                  ·
                    refine ⟨462823734007500635429789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4936786496080006777917749 462823734007500635429789)
                    ·
                      rfl

theorem cell22_1352019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_1352019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352019 prefixEnd_1352019 := by exact prefixLift 1352019
  have htrace : WordTrace (prefixWord ++ tailWord_1352019) baseStart_1352019 baseEnd_1352019 := by
    simpa [prefixWord, tailWord_1352019, baseEnd_1352019] using wordTrace_append hprefix tailTrace_1352019
  have hstable : (prefixWord ++ tailWord_1352019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352019).length < 2 ^ (prefixWord ++ tailWord_1352019).sum := by decide
  have hdescent : baseEnd_1352019 < baseStart_1352019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352036 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1352036 : Nat := 118140960795 + 1352036 * 2 ^ 59
def prefixEnd_1352036 : Nat := 4983230072969 + 3 ^ 40 * 1352036 * 2
def baseEnd_1352036 : Nat := 462829553454918257754737

theorem tailTrace_1352036 : CollatzResearch.WordTrace tailWord_1352036 prefixEnd_1352036 462829553454918257754737 := by
  unfold tailWord_1352036
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656402064905978105137981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32875202753207970806850641 24656402064905978105137981)
  ·
    refine ⟨9246150774339741789426743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24656402064905978105137981 9246150774339741789426743)
    ·
      refine ⟨13869226161509612684140115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246150774339741789426743 13869226161509612684140115)
      ·
        refine ⟨20803839242264419026210173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13869226161509612684140115 20803839242264419026210173)
        ·
          refine ⟨7801439715849157134828815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20803839242264419026210173 7801439715849157134828815)
          ·
            refine ⟨11702159573773735702243223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801439715849157134828815 11702159573773735702243223)
            ·
              refine ⟨17553239360660603553364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11702159573773735702243223 17553239360660603553364835)
              ·
                refine ⟨26329859040990905330047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17553239360660603553364835 26329859040990905330047253)
                ·
                  refine ⟨1234212142546448687345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26329859040990905330047253 1234212142546448687345965)
                  ·
                    refine ⟨462829553454918257754737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234212142546448687345965 462829553454918257754737)
                    ·
                      rfl

theorem cell22_1352036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1352036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352036 prefixEnd_1352036 := by exact prefixLift 1352036
  have htrace : WordTrace (prefixWord ++ tailWord_1352036) baseStart_1352036 baseEnd_1352036 := by
    simpa [prefixWord, tailWord_1352036, baseEnd_1352036] using wordTrace_append hprefix tailTrace_1352036
  have hstable : (prefixWord ++ tailWord_1352036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352036).length < 2 ^ (prefixWord ++ tailWord_1352036).sum := by decide
  have hdescent : baseEnd_1352036 < baseStart_1352036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352053 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1352053 : Nat := 118140960795 + 1352053 * 2 ^ 59
def prefixEnd_1352053 : Nat := 4983230072969 + 3 ^ 40 * 1352053 * 2
def baseEnd_1352053 : Nat := 462835372902335880079685

theorem tailTrace_1352053 : CollatzResearch.WordTrace tailWord_1352053 prefixEnd_1352053 462835372902335880079685 := by
  unfold tailWord_1352053
  simp only [CollatzResearch.WordTrace]
  refine ⟨49313424170750368113644813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32875616113833578742429875 49313424170750368113644813)
  ·
    refine ⟨18492534064031388042616805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49313424170750368113644813 18492534064031388042616805)
    ·
      refine ⟨3467350137005885257990651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18492534064031388042616805 3467350137005885257990651)
      ·
        refine ⟨5201025205508827886985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467350137005885257990651 5201025205508827886985977)
        ·
          refine ⟨3900768904131620915239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5201025205508827886985977 3900768904131620915239483)
          ·
            refine ⟨5851153356197431372859225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900768904131620915239483 5851153356197431372859225)
            ·
              refine ⟨4388365017148073529644419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851153356197431372859225 4388365017148073529644419)
              ·
                refine ⟨6582547525722110294466629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388365017148073529644419 6582547525722110294466629)
                ·
                  refine ⟨1234227661072895680212493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6582547525722110294466629 1234227661072895680212493)
                  ·
                    refine ⟨462835372902335880079685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234227661072895680212493 462835372902335880079685)
                    ·
                      rfl

theorem cell22_1352053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1352053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352053 prefixEnd_1352053 := by exact prefixLift 1352053
  have htrace : WordTrace (prefixWord ++ tailWord_1352053) baseStart_1352053 baseEnd_1352053 := by
    simpa [prefixWord, tailWord_1352053, baseEnd_1352053] using wordTrace_append hprefix tailTrace_1352053
  have hstable : (prefixWord ++ tailWord_1352053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352053).length < 2 ^ (prefixWord ++ tailWord_1352053).sum := by decide
  have hdescent : baseEnd_1352053 < baseStart_1352053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352106 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_1352106 : Nat := 118140960795 + 1352106 * 2 ^ 59
def prefixEnd_1352106 : Nat := 4983230072969 + 3 ^ 40 * 1352106 * 2
def baseEnd_1352106 : Nat := 154284505295153802834841

theorem tailTrace_1352106 : CollatzResearch.WordTrace tailWord_1352106 prefixEnd_1352106 154284505295153802834841 := by
  unfold tailWord_1352106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328839309889589541331043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32876904826372238776882781 12328839309889589541331043)
  ·
    refine ⟨18493258964834384311996565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12328839309889589541331043 18493258964834384311996565)
    ·
      refine ⟨866871513976611764624839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18493258964834384311996565 866871513976611764624839)
      ·
        refine ⟨1300307270964917646937259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866871513976611764624839 1300307270964917646937259)
        ·
          refine ⟨1950460906447376470405889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300307270964917646937259 1950460906447376470405889)
          ·
            refine ⟨1462845679835532352804417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950460906447376470405889 1462845679835532352804417)
            ·
              refine ⟨1097134259876649264603313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462845679835532352804417 1097134259876649264603313)
              ·
                refine ⟨822850694907486948452485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097134259876649264603313 822850694907486948452485)
                ·
                  refine ⟨154284505295153802834841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822850694907486948452485 154284505295153802834841)
                  ·
                    rfl

theorem cell22_1352106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_1352106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352106 prefixEnd_1352106 := by exact prefixLift 1352106
  have htrace : WordTrace (prefixWord ++ tailWord_1352106) baseStart_1352106 baseEnd_1352106 := by
    simpa [prefixWord, tailWord_1352106, baseEnd_1352106] using wordTrace_append hprefix tailTrace_1352106
  have hstable : (prefixWord ++ tailWord_1352106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352106).length < 2 ^ (prefixWord ++ tailWord_1352106).sum := by decide
  have hdescent : baseEnd_1352106 < baseStart_1352106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352126 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1352126 : Nat := 118140960795 + 1352126 * 2 ^ 59
def prefixEnd_1352126 : Nat := 4983230072969 + 3 ^ 40 * 1352126 * 2
def baseEnd_1352126 : Nat := 462860362294188023004461

theorem tailTrace_1352126 : CollatzResearch.WordTrace tailWord_1352126 prefixEnd_1352126 462860362294188023004461 := by
  unfold tailWord_1352126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164510837435737697631529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32877391132990601054034821 6164510837435737697631529)
  ·
    refine ⟨4623383128076803273223647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6164510837435737697631529 4623383128076803273223647)
    ·
      refine ⟨6935074692115204909835471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623383128076803273223647 6935074692115204909835471)
      ·
        refine ⟨10402612038172807364753207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935074692115204909835471 10402612038172807364753207)
        ·
          refine ⟨15603918057259211047129811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402612038172807364753207 15603918057259211047129811)
          ·
            refine ⟨23405877085888816570694717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15603918057259211047129811 23405877085888816570694717)
            ·
              refine ⟨8777203907208306214010519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23405877085888816570694717 8777203907208306214010519)
              ·
                refine ⟨13165805860812459321015779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8777203907208306214010519 13165805860812459321015779)
                ·
                  refine ⟨19748708791218688981523669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13165805860812459321015779 19748708791218688981523669)
                  ·
                    refine ⟨462860362294188023004461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19748708791218688981523669 462860362294188023004461)
                    ·
                      rfl

theorem cell22_1352126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1352126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352126 prefixEnd_1352126 := by exact prefixLift 1352126
  have htrace : WordTrace (prefixWord ++ tailWord_1352126) baseStart_1352126 baseEnd_1352126 := by
    simpa [prefixWord, tailWord_1352126, baseEnd_1352126] using wordTrace_append hprefix tailTrace_1352126
  have hstable : (prefixWord ++ tailWord_1352126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352126).length < 2 ^ (prefixWord ++ tailWord_1352126).sum := by decide
  have hdescent : baseEnd_1352126 < baseStart_1352126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352173 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1352173 : Nat := 118140960795 + 1352173 * 2 ^ 59
def prefixEnd_1352173 : Nat := 4983230072969 + 3 ^ 40 * 1352173 * 2
def baseEnd_1352173 : Nat := 154292150451565189026439

theorem tailTrace_1352173 : CollatzResearch.WordTrace tailWord_1352173 prefixEnd_1352173 154292150451565189026439 := by
  unfold tailWord_1352173
  simp only [CollatzResearch.WordTrace]
  refine ⟨49317800930315628608013173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32878533953543752405342115 49317800930315628608013173)
  ·
    refine ⟨4623543837217090182001235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49317800930315628608013173 4623543837217090182001235)
    ·
      refine ⟨6935315755825635273001853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623543837217090182001235 6935315755825635273001853)
      ·
        refine ⟨2600743408434613227375695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6935315755825635273001853 2600743408434613227375695)
        ·
          refine ⟨3901115112651919841063543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600743408434613227375695 3901115112651919841063543)
          ·
            refine ⟨5851672668977879761595315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901115112651919841063543 5851672668977879761595315)
            ·
              refine ⟨8777509003466819642392973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851672668977879761595315 8777509003466819642392973)
              ·
                refine ⟨3291565876300057365897365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8777509003466819642392973 3291565876300057365897365)
                ·
                  refine ⟨154292150451565189026439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3291565876300057365897365 154292150451565189026439)
                  ·
                    rfl

theorem cell22_1352173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1352173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352173 prefixEnd_1352173 := by exact prefixLift 1352173
  have htrace : WordTrace (prefixWord ++ tailWord_1352173) baseStart_1352173 baseEnd_1352173 := by
    simpa [prefixWord, tailWord_1352173, baseEnd_1352173] using wordTrace_append hprefix tailTrace_1352173
  have hstable : (prefixWord ++ tailWord_1352173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352173).length < 2 ^ (prefixWord ++ tailWord_1352173).sum := by decide
  have hdescent : baseEnd_1352173 < baseStart_1352173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352186 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_1352186 : Nat := 118140960795 + 1352186 * 2 ^ 59
def prefixEnd_1352186 : Nat := 4983230072969 + 3 ^ 40 * 1352186 * 2
def baseEnd_1352186 : Nat := 462880901520367866504277

theorem tailTrace_1352186 : CollatzResearch.WordTrace tailWord_1352186 prefixEnd_1352186 462880901520367866504277 := by
  unfold tailWord_1352186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329568769817132957059103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32878850052845687885490941 12329568769817132957059103)
  ·
    refine ⟨18494353154725699435588655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12329568769817132957059103 18494353154725699435588655)
    ·
      refine ⟨27741529732088549153382983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18494353154725699435588655 27741529732088549153382983)
      ·
        refine ⟨41612294598132823730074475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27741529732088549153382983 41612294598132823730074475)
        ·
          refine ⟨62418441897199235595111713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41612294598132823730074475 62418441897199235595111713)
          ·
            refine ⟨46813831422899426696333785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62418441897199235595111713 46813831422899426696333785)
            ·
              refine ⟨35110373567174570022250339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46813831422899426696333785 35110373567174570022250339)
              ·
                refine ⟨52665560350761855033375509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35110373567174570022250339 52665560350761855033375509)
                ·
                  refine ⟨2468698141441961954689477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52665560350761855033375509 2468698141441961954689477)
                  ·
                    refine ⟨462880901520367866504277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2468698141441961954689477 462880901520367866504277)
                    ·
                      rfl

theorem cell22_1352186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_1352186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352186 prefixEnd_1352186 := by exact prefixLift 1352186
  have htrace : WordTrace (prefixWord ++ tailWord_1352186) baseStart_1352186 baseEnd_1352186 := by
    simpa [prefixWord, tailWord_1352186, baseEnd_1352186] using wordTrace_append hprefix tailTrace_1352186
  have hstable : (prefixWord ++ tailWord_1352186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352186).length < 2 ^ (prefixWord ++ tailWord_1352186).sum := by decide
  have hdescent : baseEnd_1352186 < baseStart_1352186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352284 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1352284 : Nat := 118140960795 + 1352284 * 2 ^ 59
def prefixEnd_1352284 : Nat := 4983230072969 + 3 ^ 40 * 1352284 * 2
def baseEnd_1352284 : Nat := 462914448923128277553977

theorem tailTrace_1352284 : CollatzResearch.WordTrace tailWord_1352284 prefixEnd_1352284 462914448923128277553977 := by
  unfold tailWord_1352284
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660924716456747282651953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32881232955275663043535937 24660924716456747282651953)
  ·
    refine ⟨18495693537342560461988965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24660924716456747282651953 18495693537342560461988965)
    ·
      refine ⟨3467942538251730086622931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18495693537342560461988965 3467942538251730086622931)
      ·
        refine ⟨5201913807377595129934397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467942538251730086622931 5201913807377595129934397)
        ·
          refine ⟨1950717677766598173725399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5201913807377595129934397 1950717677766598173725399)
          ·
            refine ⟨2926076516649897260588099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950717677766598173725399 2926076516649897260588099)
            ·
              refine ⟨4389114774974845890882149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926076516649897260588099 4389114774974845890882149)
              ·
                refine ⟨822959020307783604540403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4389114774974845890882149 822959020307783604540403)
                ·
                  refine ⟨1234438530461675406810605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822959020307783604540403 1234438530461675406810605)
                  ·
                    refine ⟨462914448923128277553977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234438530461675406810605 462914448923128277553977)
                    ·
                      rfl

theorem cell22_1352284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1352284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352284 prefixEnd_1352284 := by exact prefixLift 1352284
  have htrace : WordTrace (prefixWord ++ tailWord_1352284) baseStart_1352284 baseEnd_1352284 := by
    simpa [prefixWord, tailWord_1352284, baseEnd_1352284] using wordTrace_append hprefix tailTrace_1352284
  have hstable : (prefixWord ++ tailWord_1352284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352284).length < 2 ^ (prefixWord ++ tailWord_1352284).sum := by decide
  have hdescent : baseEnd_1352284 < baseStart_1352284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352286 : List Nat := [4, 4, 1, 2, 2, 1, 1, 7]
def baseStart_1352286 : Nat := 118140960795 + 1352286 * 2 ^ 59
def prefixEnd_1352286 : Nat := 4983230072969 + 3 ^ 40 * 1352286 * 2
def baseEnd_1352286 : Nat := 51435014840444548778219

theorem tailTrace_1352286 : CollatzResearch.WordTrace tailWord_1352286 prefixEnd_1352286 51435014840444548778219 := by
  unfold tailWord_1352286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165240297363281113359589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32881281585937499271251141 6165240297363281113359589)
  ·
    refine ⟨1155982555755615208754923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6165240297363281113359589 1155982555755615208754923)
    ·
      refine ⟨1733973833633422813132385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155982555755615208754923 1733973833633422813132385)
      ·
        refine ⟨1300480375225067109849289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733973833633422813132385 1300480375225067109849289)
        ·
          refine ⟨975360281418800332386967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300480375225067109849289 975360281418800332386967)
          ·
            refine ⟨1463040422128200498580451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975360281418800332386967 1463040422128200498580451)
            ·
              refine ⟨2194560633192300747870677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463040422128200498580451 2194560633192300747870677)
              ·
                refine ⟨51435014840444548778219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2194560633192300747870677 51435014840444548778219)
                ·
                  rfl

theorem cell22_1352286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_1352286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352286 prefixEnd_1352286 := by exact prefixLift 1352286
  have htrace : WordTrace (prefixWord ++ tailWord_1352286) baseStart_1352286 baseEnd_1352286 := by
    simpa [prefixWord, tailWord_1352286, baseEnd_1352286] using wordTrace_append hprefix tailTrace_1352286
  have hstable : (prefixWord ++ tailWord_1352286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352286).length < 2 ^ (prefixWord ++ tailWord_1352286).sum := by decide
  have hdescent : baseEnd_1352286 < baseStart_1352286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352323 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_1352323 : Nat := 118140960795 + 1352323 * 2 ^ 59
def prefixEnd_1352323 : Nat := 4983230072969 + 3 ^ 40 * 1352323 * 2
def baseEnd_1352323 : Nat := 462927799420145175828857

theorem tailTrace_1352323 : CollatzResearch.WordTrace tailWord_1352323 prefixEnd_1352323 462927799420145175828857 := by
  unfold tailWord_1352323
  simp only [CollatzResearch.WordTrace]
  refine ⟨49323271879772204225973623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32882181253181469483982415 49323271879772204225973623)
  ·
    refine ⟨73984907819658306338960435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49323271879772204225973623 73984907819658306338960435)
    ·
      refine ⟨110977361729487459508440653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73984907819658306338960435 110977361729487459508440653)
      ·
        refine ⟨41616510648557797315665245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110977361729487459508440653 41616510648557797315665245)
        ·
          refine ⟨15606191493209173993374467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41616510648557797315665245 15606191493209173993374467)
          ·
            refine ⟨23409287239813760990061701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15606191493209173993374467 23409287239813760990061701)
            ·
              refine ⟨4389241357465080185636569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23409287239813760990061701 4389241357465080185636569)
              ·
                refine ⟨3291931018098810139227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389241357465080185636569 3291931018098810139227427)
                ·
                  refine ⟨4937896527148215208841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291931018098810139227427 4937896527148215208841141)
                  ·
                    refine ⟨462927799420145175828857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4937896527148215208841141 462927799420145175828857)
                    ·
                      rfl

theorem cell22_1352323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_1352323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352323 prefixEnd_1352323 := by exact prefixLift 1352323
  have htrace : WordTrace (prefixWord ++ tailWord_1352323) baseStart_1352323 baseEnd_1352323 := by
    simpa [prefixWord, tailWord_1352323, baseEnd_1352323] using wordTrace_append hprefix tailTrace_1352323
  have hstable : (prefixWord ++ tailWord_1352323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352323).length < 2 ^ (prefixWord ++ tailWord_1352323).sum := by decide
  have hdescent : baseEnd_1352323 < baseStart_1352323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352325 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 4]
def baseStart_1352325 : Nat := 118140960795 + 1352325 * 2 ^ 59
def prefixEnd_1352325 : Nat := 4983230072969 + 3 ^ 40 * 1352325 * 2
def baseEnd_1352325 : Nat := 154309494687005945759617

theorem tailTrace_1352325 : CollatzResearch.WordTrace tailWord_1352325 prefixEnd_1352325 154309494687005945759617 := by
  unfold tailWord_1352325
  simp only [CollatzResearch.WordTrace]
  refine ⟨49323344825764958567546429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32882229883843305711697619 49323344825764958567546429)
  ·
    refine ⟨18496254309661859462829911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49323344825764958567546429 18496254309661859462829911)
    ·
      refine ⟨27744381464492789194244867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18496254309661859462829911 27744381464492789194244867)
      ·
        refine ⟨41616572196739183791367301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27744381464492789194244867 41616572196739183791367301)
        ·
          refine ⟨7803107286888596960881369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41616572196739183791367301 7803107286888596960881369)
          ·
            refine ⟨5852330465166447720661027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7803107286888596960881369 5852330465166447720661027)
            ·
              refine ⟨8778495697749671580991541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852330465166447720661027 8778495697749671580991541)
              ·
                refine ⟨822983971664031710717957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8778495697749671580991541 822983971664031710717957)
                ·
                  refine ⟨154309494687005945759617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 822983971664031710717957 154309494687005945759617)
                  ·
                    rfl

theorem cell22_1352325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_1352325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352325 prefixEnd_1352325 := by exact prefixLift 1352325
  have htrace : WordTrace (prefixWord ++ tailWord_1352325) baseStart_1352325 baseEnd_1352325 := by
    simpa [prefixWord, tailWord_1352325, baseEnd_1352325] using wordTrace_append hprefix tailTrace_1352325
  have hstable : (prefixWord ++ tailWord_1352325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352325).length < 2 ^ (prefixWord ++ tailWord_1352325).sum := by decide
  have hdescent : baseEnd_1352325 < baseStart_1352325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352415 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 5]
def baseStart_1352415 : Nat := 118140960795 + 1352415 * 2 ^ 59
def prefixEnd_1352415 : Nat := 4983230072969 + 3 ^ 40 * 1352415 * 2
def baseEnd_1352415 : Nat := 154319764300095867509525

theorem tailTrace_1352415 : CollatzResearch.WordTrace tailWord_1352415 prefixEnd_1352415 154319764300095867509525 := by
  unfold tailWord_1352415
  simp only [CollatzResearch.WordTrace]
  refine ⟨49326627395438903938322699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32884418263625935958881799 49326627395438903938322699)
  ·
    refine ⟨73989941093158355907484049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49326627395438903938322699 73989941093158355907484049)
    ·
      refine ⟨55492455819868766930613037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73989941093158355907484049 55492455819868766930613037)
      ·
        refine ⟨20809670932450787598979889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55492455819868766930613037 20809670932450787598979889)
        ·
          refine ⟨15607253199338090699234917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20809670932450787598979889 15607253199338090699234917)
          ·
            refine ⟨2926359974875892006106547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15607253199338090699234917 2926359974875892006106547)
            ·
              refine ⟨4389539962313838009159821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926359974875892006106547 4389539962313838009159821)
              ·
                refine ⟨1646077485867689253434933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389539962313838009159821 1646077485867689253434933)
                ·
                  refine ⟨154319764300095867509525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1646077485867689253434933 154319764300095867509525)
                  ·
                    rfl

theorem cell22_1352415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].length) (baseStart_1352415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352415 prefixEnd_1352415 := by exact prefixLift 1352415
  have htrace : WordTrace (prefixWord ++ tailWord_1352415) baseStart_1352415 baseEnd_1352415 := by
    simpa [prefixWord, tailWord_1352415, baseEnd_1352415] using wordTrace_append hprefix tailTrace_1352415
  have hstable : (prefixWord ++ tailWord_1352415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352415).length < 2 ^ (prefixWord ++ tailWord_1352415).sum := by decide
  have hdescent : baseEnd_1352415 < baseStart_1352415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352494 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1352494 : Nat := 118140960795 + 1352494 * 2 ^ 59
def prefixEnd_1352494 : Nat := 4983230072969 + 3 ^ 40 * 1352494 * 2
def baseEnd_1352494 : Nat := 154328778738252576601111

theorem tailTrace_1352494 : CollatzResearch.WordTrace tailWord_1352494 prefixEnd_1352494 154328778738252576601111 := by
  unfold tailWord_1352494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166188595269087553806067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32886339174768466953632357 6166188595269087553806067)
  ·
    refine ⟨9249282892903631330709101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6166188595269087553806067 9249282892903631330709101)
    ·
      refine ⟨3468481084838861749015913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9249282892903631330709101 3468481084838861749015913)
      ·
        refine ⟨2601360813629146311761935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3468481084838861749015913 2601360813629146311761935)
        ·
          refine ⟨3902041220443719467642903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601360813629146311761935 3902041220443719467642903)
          ·
            refine ⟨5853061830665579201464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902041220443719467642903 5853061830665579201464355)
            ·
              refine ⟨8779592745998368802196533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853061830665579201464355 8779592745998368802196533)
              ·
                refine ⟨823086819937347075205925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8779592745998368802196533 823086819937347075205925)
                ·
                  refine ⟨154328778738252576601111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823086819937347075205925 154328778738252576601111)
                  ·
                    rfl

theorem cell22_1352494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1352494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352494 prefixEnd_1352494 := by exact prefixLift 1352494
  have htrace : WordTrace (prefixWord ++ tailWord_1352494) baseStart_1352494 baseEnd_1352494 := by
    simpa [prefixWord, tailWord_1352494, baseEnd_1352494] using wordTrace_append hprefix tailTrace_1352494
  have hstable : (prefixWord ++ tailWord_1352494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352494).length < 2 ^ (prefixWord ++ tailWord_1352494).sum := by decide
  have hdescent : baseEnd_1352494 < baseStart_1352494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352509 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1352509 : Nat := 118140960795 + 1352509 * 2 ^ 59
def prefixEnd_1352509 : Nat := 4983230072969 + 3 ^ 40 * 1352509 * 2
def baseEnd_1352509 : Nat := 462991471021302690678287

theorem tailTrace_1352509 : CollatzResearch.WordTrace tailWord_1352509 prefixEnd_1352509 462991471021302690678287 := by
  unfold tailWord_1352509
  simp only [CollatzResearch.WordTrace]
  refine ⟨49330055857098357992244581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32886703904732238661496387 49330055857098357992244581)
  ·
    refine ⟨9249385473205942123545859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49330055857098357992244581 9249385473205942123545859)
    ·
      refine ⟨13874078209808913185318789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9249385473205942123545859 13874078209808913185318789)
      ·
        refine ⟨2601389664339171222247273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13874078209808913185318789 2601389664339171222247273)
        ·
          refine ⟨1951042248254378416685455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2601389664339171222247273 1951042248254378416685455)
          ·
            refine ⟨2926563372381567625028183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951042248254378416685455 2926563372381567625028183)
            ·
              refine ⟨4389845058572351437542275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926563372381567625028183 4389845058572351437542275)
              ·
                refine ⟨6584767587858527156313413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389845058572351437542275 6584767587858527156313413)
                ·
                  refine ⟨1234643922723473841808765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6584767587858527156313413 1234643922723473841808765)
                  ·
                    refine ⟨462991471021302690678287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234643922723473841808765 462991471021302690678287)
                    ·
                      rfl

theorem cell22_1352509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1352509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352509 prefixEnd_1352509 := by exact prefixLift 1352509
  have htrace : WordTrace (prefixWord ++ tailWord_1352509) baseStart_1352509 baseEnd_1352509 := by
    simpa [prefixWord, tailWord_1352509, baseEnd_1352509] using wordTrace_append hprefix tailTrace_1352509
  have hstable : (prefixWord ++ tailWord_1352509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352509).length < 2 ^ (prefixWord ++ tailWord_1352509).sum := by decide
  have hdescent : baseEnd_1352509 < baseStart_1352509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352537 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_1352537 : Nat := 118140960795 + 1352537 * 2 ^ 59
def prefixEnd_1352537 : Nat := 4983230072969 + 3 ^ 40 * 1352537 * 2
def baseEnd_1352537 : Nat := 463001055993519950978201

theorem tailTrace_1352537 : CollatzResearch.WordTrace tailWord_1352537 prefixEnd_1352537 463001055993519950978201 := by
  unfold tailWord_1352537
  simp only [CollatzResearch.WordTrace]
  refine ⟨49331077100996918774263865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32887384733997945849509243 49331077100996918774263865)
  ·
    refine ⟨36998307825747689080697899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49331077100996918774263865 36998307825747689080697899)
    ·
      refine ⟨55497461738621533621046849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36998307825747689080697899 55497461738621533621046849)
      ·
        refine ⟨41623096303966150215785137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55497461738621533621046849 41623096303966150215785137)
        ·
          refine ⟨31217322227974612661838853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41623096303966150215785137 31217322227974612661838853)
          ·
            refine ⟨5853247917745239874094785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31217322227974612661838853 5853247917745239874094785)
            ·
              refine ⟨4389935938308929905571089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853247917745239874094785 4389935938308929905571089)
              ·
                refine ⟨3292451953731697429178317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389935938308929905571089 3292451953731697429178317)
                ·
                  refine ⟨1234669482649386535941869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3292451953731697429178317 1234669482649386535941869)
                  ·
                    refine ⟨463001055993519950978201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234669482649386535941869 463001055993519950978201)
                    ·
                      rfl

theorem cell22_1352537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_1352537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352537 prefixEnd_1352537 := by exact prefixLift 1352537
  have htrace : WordTrace (prefixWord ++ tailWord_1352537) baseStart_1352537 baseEnd_1352537 := by
    simpa [prefixWord, tailWord_1352537, baseEnd_1352537] using wordTrace_append hprefix tailTrace_1352537
  have hstable : (prefixWord ++ tailWord_1352537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352537).length < 2 ^ (prefixWord ++ tailWord_1352537).sum := by decide
  have hdescent : baseEnd_1352537 < baseStart_1352537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352580 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1352580 : Nat := 118140960795 + 1352580 * 2 ^ 59
def prefixEnd_1352580 : Nat := 4983230072969 + 3 ^ 40 * 1352580 * 2
def baseEnd_1352580 : Nat := 463015775772282172153069

theorem tailTrace_1352580 : CollatzResearch.WordTrace tailWord_1352580 prefixEnd_1352580 463015775772282172153069 := by
  unfold tailWord_1352580
  simp only [CollatzResearch.WordTrace]
  refine ⟨24666322719920568559039597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32888430293227424745386129 24666322719920568559039597)
  ·
    refine ⟨9249871019970213209639849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24666322719920568559039597 9249871019970213209639849)
    ·
      refine ⟨6937403264977659907229887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9249871019970213209639849 6937403264977659907229887)
      ·
        refine ⟨10406104897466489860844831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937403264977659907229887 10406104897466489860844831)
        ·
          refine ⟨15609157346199734791267247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10406104897466489860844831 15609157346199734791267247)
          ·
            refine ⟨23413736019299602186900871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609157346199734791267247 23413736019299602186900871)
            ·
              refine ⟨35120604028949403280351307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23413736019299602186900871 35120604028949403280351307)
              ·
                refine ⟨52680906043424104920526961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35120604028949403280351307 52680906043424104920526961)
                ·
                  refine ⟨39510679532568078690395221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52680906043424104920526961 39510679532568078690395221)
                  ·
                    refine ⟨463015775772282172153069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39510679532568078690395221 463015775772282172153069)
                    ·
                      rfl

theorem cell22_1352580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1352580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352580 prefixEnd_1352580 := by exact prefixLift 1352580
  have htrace : WordTrace (prefixWord ++ tailWord_1352580) baseStart_1352580 baseEnd_1352580 := by
    simpa [prefixWord, tailWord_1352580, baseEnd_1352580] using wordTrace_append hprefix tailTrace_1352580
  have hstable : (prefixWord ++ tailWord_1352580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352580).length < 2 ^ (prefixWord ++ tailWord_1352580).sum := by decide
  have hdescent : baseEnd_1352580 < baseStart_1352580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352584 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_1352584 : Nat := 118140960795 + 1352584 * 2 ^ 59
def prefixEnd_1352584 : Nat := 4983230072969 + 3 ^ 40 * 1352584 * 2
def baseEnd_1352584 : Nat := 154339048351342498351019

theorem tailTrace_1352584 : CollatzResearch.WordTrace tailWord_1352584 prefixEnd_1352584 154339048351342498351019 := by
  unfold tailWord_1352584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24666395665913322900612403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32888527554551097200816537 24666395665913322900612403)
  ·
    refine ⟨36999593498869984350918605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24666395665913322900612403 36999593498869984350918605)
    ·
      refine ⟨13874847562076244131594477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36999593498869984350918605 13874847562076244131594477)
      ·
        refine ⟨5203067835778591549347929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13874847562076244131594477 5203067835778591549347929)
        ·
          refine ⟨3902300876833943662010947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5203067835778591549347929 3902300876833943662010947)
          ·
            refine ⟨5853451315250915493016421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902300876833943662010947 5853451315250915493016421)
            ·
              refine ⟨1097522121609546654940579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5853451315250915493016421 1097522121609546654940579)
              ·
                refine ⟨1646283182414319982410869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097522121609546654940579 1646283182414319982410869)
                ·
                  refine ⟨154339048351342498351019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1646283182414319982410869 154339048351342498351019)
                  ·
                    rfl

theorem cell22_1352584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_1352584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352584 prefixEnd_1352584 := by exact prefixLift 1352584
  have htrace : WordTrace (prefixWord ++ tailWord_1352584) baseStart_1352584 baseEnd_1352584 := by
    simpa [prefixWord, tailWord_1352584, baseEnd_1352584] using wordTrace_append hprefix tailTrace_1352584
  have hstable : (prefixWord ++ tailWord_1352584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352584).length < 2 ^ (prefixWord ++ tailWord_1352584).sum := by decide
  have hdescent : baseEnd_1352584 < baseStart_1352584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352597 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1352597 : Nat := 118140960795 + 1352597 * 2 ^ 59
def prefixEnd_1352597 : Nat := 4983230072969 + 3 ^ 40 * 1352597 * 2
def baseEnd_1352597 : Nat := 463021595219699794478017

theorem tailTrace_1352597 : CollatzResearch.WordTrace tailWord_1352597 prefixEnd_1352597 463021595219699794478017 := by
  unfold tailWord_1352597
  simp only [CollatzResearch.WordTrace]
  refine ⟨49333265480779549021448045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32888843653853032680965363 49333265480779549021448045)
  ·
    refine ⟨18499974555292330883043017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49333265480779549021448045 18499974555292330883043017)
    ·
      refine ⟨13874980916469248162282263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18499974555292330883043017 13874980916469248162282263)
      ·
        refine ⟨20812471374703872243423395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13874980916469248162282263 20812471374703872243423395)
        ·
          refine ⟨31218707062055808365135093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20812471374703872243423395 31218707062055808365135093)
          ·
            refine ⟨2926753787067732034231415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31218707062055808365135093 2926753787067732034231415)
            ·
              refine ⟨4390130680601598051347123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926753787067732034231415 4390130680601598051347123)
              ·
                refine ⟨6585196020902397077020685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390130680601598051347123 6585196020902397077020685)
                ·
                  refine ⟨2469448507838398903882757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6585196020902397077020685 2469448507838398903882757)
                  ·
                    refine ⟨463021595219699794478017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469448507838398903882757 463021595219699794478017)
                    ·
                      rfl

theorem cell22_1352597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1352597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352597 prefixEnd_1352597 := by exact prefixLift 1352597
  have htrace : WordTrace (prefixWord ++ tailWord_1352597) baseStart_1352597 baseEnd_1352597 := by
    simpa [prefixWord, tailWord_1352597, baseEnd_1352597] using wordTrace_append hprefix tailTrace_1352597
  have hstable : (prefixWord ++ tailWord_1352597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352597).length < 2 ^ (prefixWord ++ tailWord_1352597).sum := by decide
  have hdescent : baseEnd_1352597 < baseStart_1352597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352629 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1352629 : Nat := 118140960795 + 1352629 * 2 ^ 59
def prefixEnd_1352629 : Nat := 4983230072969 + 3 ^ 40 * 1352629 * 2
def baseEnd_1352629 : Nat := 154344183157887459225973

theorem tailTrace_1352629 : CollatzResearch.WordTrace tailWord_1352629 prefixEnd_1352629 154344183157887459225973 := by
  unfold tailWord_1352629
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334432616663618486612941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32889621744442412324408627 49334432616663618486612941)
  ·
    refine ⟨18500412231248856932479853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49334432616663618486612941 18500412231248856932479853)
    ·
      refine ⟨6937654586718321349679945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18500412231248856932479853 6937654586718321349679945)
      ·
        refine ⟨5203240940038741012259959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6937654586718321349679945 5203240940038741012259959)
        ·
          refine ⟨7804861410058111518389939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203240940038741012259959 7804861410058111518389939)
          ·
            refine ⟨11707292115087167277584909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7804861410058111518389939 11707292115087167277584909)
            ·
              refine ⟨4390234543157687729094341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11707292115087167277584909 4390234543157687729094341)
              ·
                refine ⟨823168976842066449205189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4390234543157687729094341 823168976842066449205189)
                ·
                  refine ⟨154344183157887459225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823168976842066449205189 154344183157887459225973)
                  ·
                    rfl

theorem cell22_1352629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1352629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352629 prefixEnd_1352629 := by exact prefixLift 1352629
  have htrace : WordTrace (prefixWord ++ tailWord_1352629) baseStart_1352629 baseEnd_1352629 := by
    simpa [prefixWord, tailWord_1352629, baseEnd_1352629] using wordTrace_append hprefix tailTrace_1352629
  have hstable : (prefixWord ++ tailWord_1352629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352629).length < 2 ^ (prefixWord ++ tailWord_1352629).sum := by decide
  have hdescent : baseEnd_1352629 < baseStart_1352629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352657 : List Nat := [1, 2, 2, 1, 2, 1, 7, 6]
def baseStart_1352657 : Nat := 118140960795 + 1352657 * 2 ^ 59
def prefixEnd_1352657 : Nat := 4983230072969 + 3 ^ 40 * 1352657 * 2
def baseEnd_1352657 : Nat := 51449126049542181997537

theorem tailTrace_1352657 : CollatzResearch.WordTrace tailWord_1352657 prefixEnd_1352657 51449126049542181997537 := by
  unfold tailWord_1352657
  simp only [CollatzResearch.WordTrace]
  refine ⟨49335453860562179268632225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32890302573708119512421483 49335453860562179268632225)
  ·
    refine ⟨37001590395421634451474169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49335453860562179268632225 37001590395421634451474169)
    ·
      refine ⟨27751192796566225838605627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37001590395421634451474169 27751192796566225838605627)
      ·
        refine ⟨41626789194849338757908441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27751192796566225838605627 41626789194849338757908441)
        ·
          refine ⟨31220091896137004068431331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41626789194849338757908441 31220091896137004068431331)
          ·
            refine ⟨46830137844205506102646997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31220091896137004068431331 46830137844205506102646997)
            ·
              refine ⟨1097581355723566549280789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46830137844205506102646997 1097581355723566549280789)
              ·
                refine ⟨51449126049542181997537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097581355723566549280789 51449126049542181997537)
                ·
                  rfl

theorem cell22_1352657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 6].length) (baseStart_1352657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352657 prefixEnd_1352657 := by exact prefixLift 1352657
  have htrace : WordTrace (prefixWord ++ tailWord_1352657) baseStart_1352657 baseEnd_1352657 := by
    simpa [prefixWord, tailWord_1352657, baseEnd_1352657] using wordTrace_append hprefix tailTrace_1352657
  have hstable : (prefixWord ++ tailWord_1352657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352657).length < 2 ^ (prefixWord ++ tailWord_1352657).sum := by decide
  have hdescent : baseEnd_1352657 < baseStart_1352657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352674 : List Nat := [3, 3, 3, 1, 1, 2, 9]
def baseStart_1352674 : Nat := 118140960795 + 1352674 * 2 ^ 59
def prefixEnd_1352674 : Nat := 4983230072969 + 3 ^ 40 * 1352674 * 2
def baseEnd_1352674 : Nat := 17149924218270268900103

theorem tailTrace_1352674 : CollatzResearch.WordTrace tailWord_1352674 prefixEnd_1352674 17149924218270268900103 := by
  unfold tailWord_1352674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12334018475375147793000269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32890715934333727448000717 12334018475375147793000269)
  ·
    refine ⟨4625256928265680422375101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12334018475375147793000269 4625256928265680422375101)
    ·
      refine ⟨1734471348099630158390663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4625256928265680422375101 1734471348099630158390663)
      ·
        refine ⟨2601707022149445237585995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734471348099630158390663 2601707022149445237585995)
        ·
          refine ⟨3902560533224167856378993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601707022149445237585995 3902560533224167856378993)
          ·
            refine ⟨2926920399918125892284245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3902560533224167856378993 2926920399918125892284245)
            ·
              refine ⟨17149924218270268900103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2926920399918125892284245 17149924218270268900103)
              ·
                rfl

theorem cell22_1352674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 9].length) (baseStart_1352674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352674 prefixEnd_1352674 := by exact prefixLift 1352674
  have htrace : WordTrace (prefixWord ++ tailWord_1352674) baseStart_1352674 baseEnd_1352674 := by
    simpa [prefixWord, tailWord_1352674, baseEnd_1352674] using wordTrace_append hprefix tailTrace_1352674
  have hstable : (prefixWord ++ tailWord_1352674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352674).length < 2 ^ (prefixWord ++ tailWord_1352674).sum := by decide
  have hdescent : baseEnd_1352674 < baseStart_1352674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352689 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_1352689 : Nat := 118140960795 + 1352689 * 2 ^ 59
def prefixEnd_1352689 : Nat := 4983230072969 + 3 ^ 40 * 1352689 * 2
def baseEnd_1352689 : Nat := 463053088699842221177735

theorem tailTrace_1352689 : CollatzResearch.WordTrace tailWord_1352689 prefixEnd_1352689 463053088699842221177735 := by
  unfold tailWord_1352689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49336620996446248733797121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32891080664297499155864747 49336620996446248733797121)
  ·
    refine ⟨37002465747334686550347841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49336620996446248733797121 37002465747334686550347841)
    ·
      refine ⟨27751849310501014912760881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37002465747334686550347841 27751849310501014912760881)
      ·
        refine ⟨20813886982875761184570661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27751849310501014912760881 20813886982875761184570661)
        ·
          refine ⟨3902603809289205222106999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20813886982875761184570661 3902603809289205222106999)
          ·
            refine ⟨5853905713933807833160499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902603809289205222106999 5853905713933807833160499)
            ·
              refine ⟨8780858570900711749740749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853905713933807833160499 8780858570900711749740749)
              ·
                refine ⟨3292821964087766906152781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8780858570900711749740749 3292821964087766906152781)
                ·
                  refine ⟨1234808236532912589807293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3292821964087766906152781 1234808236532912589807293)
                  ·
                    refine ⟨463053088699842221177735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234808236532912589807293 463053088699842221177735)
                    ·
                      rfl

theorem cell22_1352689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_1352689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352689 prefixEnd_1352689 := by exact prefixLift 1352689
  have htrace : WordTrace (prefixWord ++ tailWord_1352689) baseStart_1352689 baseEnd_1352689 := by
    simpa [prefixWord, tailWord_1352689, baseEnd_1352689] using wordTrace_append hprefix tailTrace_1352689
  have hstable : (prefixWord ++ tailWord_1352689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352689).length < 2 ^ (prefixWord ++ tailWord_1352689).sum := by decide
  have hdescent : baseEnd_1352689 < baseStart_1352689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352740 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_1352740 : Nat := 118140960795 + 1352740 * 2 ^ 59
def prefixEnd_1352740 : Nat := 4983230072969 + 3 ^ 40 * 1352740 * 2
def baseEnd_1352740 : Nat := 463070547042095088152579

theorem tailTrace_1352740 : CollatzResearch.WordTrace tailWord_1352740 prefixEnd_1352740 463070547042095088152579 := by
  unfold tailWord_1352740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669240559630742221951837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32892320746174322962602449 24669240559630742221951837)
  ·
    refine ⟨9250965209861528333231939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24669240559630742221951837 9250965209861528333231939)
    ·
      refine ⟨13876447814792292499847909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9250965209861528333231939 13876447814792292499847909)
      ·
        refine ⟨2601833965273554843721483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13876447814792292499847909 2601833965273554843721483)
        ·
          refine ⟨3902750947910332265582225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601833965273554843721483 3902750947910332265582225)
          ·
            refine ⟨2927063210932749199186669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3902750947910332265582225 2927063210932749199186669)
            ·
              refine ⟨1097648704099780949695001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2927063210932749199186669 1097648704099780949695001)
              ·
                refine ⟨823236528074835712271251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097648704099780949695001 823236528074835712271251)
                ·
                  refine ⟨1234854792112253568406877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823236528074835712271251 1234854792112253568406877)
                  ·
                    refine ⟨463070547042095088152579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234854792112253568406877 463070547042095088152579)
                    ·
                      rfl

theorem cell22_1352740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_1352740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352740 prefixEnd_1352740 := by exact prefixLift 1352740
  have htrace : WordTrace (prefixWord ++ tailWord_1352740) baseStart_1352740 baseEnd_1352740 := by
    simpa [prefixWord, tailWord_1352740, baseEnd_1352740] using wordTrace_append hprefix tailTrace_1352740
  have hstable : (prefixWord ++ tailWord_1352740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352740).length < 2 ^ (prefixWord ++ tailWord_1352740).sum := by decide
  have hdescent : baseEnd_1352740 < baseStart_1352740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352766 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1352766 : Nat := 118140960795 + 1352766 * 2 ^ 59
def prefixEnd_1352766 : Nat := 4983230072969 + 3 ^ 40 * 1352766 * 2
def baseEnd_1352766 : Nat := 463079447373439687002499

theorem tailTrace_1352766 : CollatzResearch.WordTrace tailWord_1352766 prefixEnd_1352766 463079447373439687002499 := by
  unfold tailWord_1352766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167428677145911360543769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32892952944778193922900101 6167428677145911360543769)
  ·
    refine ⟨4625571507859433520407827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6167428677145911360543769 4625571507859433520407827)
    ·
      refine ⟨6938357261789150280611741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625571507859433520407827 6938357261789150280611741)
      ·
        refine ⟨2601883973170931355229403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6938357261789150280611741 2601883973170931355229403)
        ·
          refine ⟨3902825959756397032844105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601883973170931355229403 3902825959756397032844105)
          ·
            refine ⟨2927119469817297774633079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3902825959756397032844105 2927119469817297774633079)
            ·
              refine ⟨4390679204725946661949619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927119469817297774633079 4390679204725946661949619)
              ·
                refine ⟨6586018807088919992924429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390679204725946661949619 6586018807088919992924429)
                ·
                  refine ⟨2469757052658344997346661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6586018807088919992924429 2469757052658344997346661)
                  ·
                    refine ⟨463079447373439687002499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469757052658344997346661 463079447373439687002499)
                    ·
                      rfl

theorem cell22_1352766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1352766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352766 prefixEnd_1352766 := by exact prefixLift 1352766
  have htrace : WordTrace (prefixWord ++ tailWord_1352766) baseStart_1352766 baseEnd_1352766 := by
    simpa [prefixWord, tailWord_1352766, baseEnd_1352766] using wordTrace_append hprefix tailTrace_1352766
  have hstable : (prefixWord ++ tailWord_1352766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352766).length < 2 ^ (prefixWord ++ tailWord_1352766).sum := by decide
  have hdescent : baseEnd_1352766 < baseStart_1352766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352809 : List Nat := [1, 2, 1, 1, 1, 8, 1, 7]
def baseStart_1352809 : Nat := 118140960795 + 1352809 * 2 ^ 59
def prefixEnd_1352809 : Nat := 4983230072969 + 3 ^ 40 * 1352809 * 2
def baseEnd_1352809 : Nat := 51454907461355767575263

theorem tailTrace_1352809 : CollatzResearch.WordTrace tailWord_1352809 prefixEnd_1352809 51454907461355767575263 := by
  unfold tailWord_1352809
  simp only [CollatzResearch.WordTrace]
  refine ⟨49340997756011509228165481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32893998504007672818776987 49340997756011509228165481)
  ·
    refine ⟨37005748317008631921124111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49340997756011509228165481 37005748317008631921124111)
    ·
      refine ⟨55508622475512947881686167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37005748317008631921124111 55508622475512947881686167)
      ·
        refine ⟨83262933713269421822529251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55508622475512947881686167 83262933713269421822529251)
        ·
          refine ⟨124894400569904132733793877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83262933713269421822529251 124894400569904132733793877)
          ·
            refine ⟨1463606256678564055474147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 124894400569904132733793877 1463606256678564055474147)
            ·
              refine ⟨2195409385017846083211221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463606256678564055474147 2195409385017846083211221)
              ·
                refine ⟨51454907461355767575263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2195409385017846083211221 51454907461355767575263)
                ·
                  rfl

theorem cell22_1352809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 7].length) (baseStart_1352809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352809 prefixEnd_1352809 := by exact prefixLift 1352809
  have htrace : WordTrace (prefixWord ++ tailWord_1352809) baseStart_1352809 baseEnd_1352809 := by
    simpa [prefixWord, tailWord_1352809, baseEnd_1352809] using wordTrace_append hprefix tailTrace_1352809
  have hstable : (prefixWord ++ tailWord_1352809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352809).length < 2 ^ (prefixWord ++ tailWord_1352809).sum := by decide
  have hdescent : baseEnd_1352809 < baseStart_1352809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352824 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1352824 : Nat := 118140960795 + 1352824 * 2 ^ 59
def prefixEnd_1352824 : Nat := 4983230072969 + 3 ^ 40 * 1352824 * 2
def baseEnd_1352824 : Nat := 463099301958746869052321

theorem tailTrace_1352824 : CollatzResearch.WordTrace tailWord_1352824 prefixEnd_1352824 463099301958746869052321 := by
  unfold tailWord_1352824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670772425478583394980763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32894363233971444526641017 24670772425478583394980763)
  ·
    refine ⟨37006158638217875092471145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24670772425478583394980763 37006158638217875092471145)
    ·
      refine ⟨27754618978663406319353359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37006158638217875092471145 27754618978663406319353359)
      ·
        refine ⟨41631928467995109479030039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27754618978663406319353359 41631928467995109479030039)
        ·
          refine ⟨62447892701992664218545059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41631928467995109479030039 62447892701992664218545059)
          ·
            refine ⟨93671839052988996327817589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62447892701992664218545059 93671839052988996327817589)
            ·
              refine ⟨8781734911217718405732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93671839052988996327817589 8781734911217718405732899)
              ·
                refine ⟨13172602366826577608599349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8781734911217718405732899 13172602366826577608599349)
                ·
                  refine ⟨1234931471889991650806189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13172602366826577608599349 1234931471889991650806189)
                  ·
                    refine ⟨463099301958746869052321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234931471889991650806189 463099301958746869052321)
                    ·
                      rfl

theorem cell22_1352824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1352824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352824 prefixEnd_1352824 := by exact prefixLift 1352824
  have htrace : WordTrace (prefixWord ++ tailWord_1352824) baseStart_1352824 baseEnd_1352824 := by
    simpa [prefixWord, tailWord_1352824, baseEnd_1352824] using wordTrace_append hprefix tailTrace_1352824
  have hstable : (prefixWord ++ tailWord_1352824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352824).length < 2 ^ (prefixWord ++ tailWord_1352824).sum := by decide
  have hdescent : baseEnd_1352824 < baseStart_1352824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352858 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_1352858 : Nat := 118140960795 + 1352858 * 2 ^ 59
def prefixEnd_1352858 : Nat := 4983230072969 + 3 ^ 40 * 1352858 * 2
def baseEnd_1352858 : Nat := 463110940853582113702217

theorem tailTrace_1352858 : CollatzResearch.WordTrace tailWord_1352858 prefixEnd_1352858 463110940853582113702217 := by
  unfold tailWord_1352858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335696233208497649174807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32895189955222660397799485 12335696233208497649174807)
  ·
    refine ⟨18503544349812746473762211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12335696233208497649174807 18503544349812746473762211)
    ·
      refine ⟨27755316524719119710643317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18503544349812746473762211 27755316524719119710643317)
      ·
        refine ⟨2602060924192417472872811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27755316524719119710643317 2602060924192417472872811)
        ·
          refine ⟨3903091386288626209309217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602060924192417472872811 3903091386288626209309217)
          ·
            refine ⟨2927318539716469656981913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903091386288626209309217 2927318539716469656981913)
            ·
              refine ⟨2195488904787352242736435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927318539716469656981913 2195488904787352242736435)
              ·
                refine ⟨3293233357181028364104653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195488904787352242736435 3293233357181028364104653)
                ·
                  refine ⟨1234962508942885636539245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3293233357181028364104653 1234962508942885636539245)
                  ·
                    refine ⟨463110940853582113702217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234962508942885636539245 463110940853582113702217)
                    ·
                      rfl

theorem cell22_1352858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_1352858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352858 prefixEnd_1352858 := by exact prefixLift 1352858
  have htrace : WordTrace (prefixWord ++ tailWord_1352858) baseStart_1352858 baseEnd_1352858 := by
    simpa [prefixWord, tailWord_1352858, baseEnd_1352858] using wordTrace_append hprefix tailTrace_1352858
  have hstable : (prefixWord ++ tailWord_1352858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352858).length < 2 ^ (prefixWord ++ tailWord_1352858).sum := by decide
  have hdescent : baseEnd_1352858 < baseStart_1352858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352869 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1352869 : Nat := 118140960795 + 1352869 * 2 ^ 59
def prefixEnd_1352869 : Nat := 4983230072969 + 3 ^ 40 * 1352869 * 2
def baseEnd_1352869 : Nat := 463114706378381751677183

theorem tailTrace_1352869 : CollatzResearch.WordTrace tailWord_1352869 prefixEnd_1352869 463114706378381751677183 := by
  unfold tailWord_1352869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49343186135794139475349661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32895457423862759650233107 49343186135794139475349661)
  ·
    refine ⟨18503694800922802303256123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49343186135794139475349661 18503694800922802303256123)
    ·
      refine ⟨27755542201384203454884185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18503694800922802303256123 27755542201384203454884185)
      ·
        refine ⟨20816656651038152591163139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27755542201384203454884185 20816656651038152591163139)
        ·
          refine ⟨31224984976557228886744709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20816656651038152591163139 31224984976557228886744709)
          ·
            refine ⟨5854684683104480416264633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31224984976557228886744709 5854684683104480416264633)
            ·
              refine ⟨4391013512328360312198475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854684683104480416264633 4391013512328360312198475)
              ·
                refine ⟨6586520268492540468297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391013512328360312198475 6586520268492540468297713)
                ·
                  refine ⟨4939890201369405351223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586520268492540468297713 4939890201369405351223285)
                  ·
                    refine ⟨463114706378381751677183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4939890201369405351223285 463114706378381751677183)
                    ·
                      rfl

theorem cell22_1352869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1352869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352869 prefixEnd_1352869 := by exact prefixLift 1352869
  have htrace : WordTrace (prefixWord ++ tailWord_1352869) baseStart_1352869 baseEnd_1352869 := by
    simpa [prefixWord, tailWord_1352869, baseEnd_1352869] using wordTrace_append hprefix tailTrace_1352869
  have hstable : (prefixWord ++ tailWord_1352869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352869).length < 2 ^ (prefixWord ++ tailWord_1352869).sum := by decide
  have hdescent : baseEnd_1352869 < baseStart_1352869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352909 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1352909 : Nat := 118140960795 + 1352909 * 2 ^ 59
def prefixEnd_1352909 : Nat := 4983230072969 + 3 ^ 40 * 1352909 * 2
def baseEnd_1352909 : Nat := 463128399195834980677061

theorem tailTrace_1352909 : CollatzResearch.WordTrace tailWord_1352909 prefixEnd_1352909 463128399195834980677061 := by
  unfold tailWord_1352909
  simp only [CollatzResearch.WordTrace]
  refine ⟨49344645055649226306805781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32896430037099484204537187 49344645055649226306805781)
  ·
    refine ⟨2313030236983557483131521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49344645055649226306805781 2313030236983557483131521)
    ·
      refine ⟨1734772677737668112348641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2313030236983557483131521 1734772677737668112348641)
      ·
        refine ⟨1301079508303251084261481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1734772677737668112348641 1301079508303251084261481)
        ·
          refine ⟨975809631227438313196111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301079508303251084261481 975809631227438313196111)
          ·
            refine ⟨1463714446841157469794167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975809631227438313196111 1463714446841157469794167)
            ·
              refine ⟨2195571670261736204691251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463714446841157469794167 2195571670261736204691251)
              ·
                refine ⟨3293357505392604307036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195571670261736204691251 3293357505392604307036877)
                ·
                  refine ⟨1235009064522226615138829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3293357505392604307036877 1235009064522226615138829)
                  ·
                    refine ⟨463128399195834980677061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235009064522226615138829 463128399195834980677061)
                    ·
                      rfl

theorem cell22_1352909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1352909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352909 prefixEnd_1352909 := by exact prefixLift 1352909
  have htrace : WordTrace (prefixWord ++ tailWord_1352909) baseStart_1352909 baseEnd_1352909 := by
    simpa [prefixWord, tailWord_1352909, baseEnd_1352909] using wordTrace_append hprefix tailTrace_1352909
  have hstable : (prefixWord ++ tailWord_1352909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352909).length < 2 ^ (prefixWord ++ tailWord_1352909).sum := by decide
  have hdescent : baseEnd_1352909 < baseStart_1352909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352935 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1352935 : Nat := 118140960795 + 1352935 * 2 ^ 59
def prefixEnd_1352935 : Nat := 4983230072969 + 3 ^ 40 * 1352935 * 2
def baseEnd_1352935 : Nat := 463137299527179579526981

theorem tailTrace_1352935 : CollatzResearch.WordTrace tailWord_1352935 prefixEnd_1352935 463137299527179579526981 := by
  unfold tailWord_1352935
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345593353555032747252259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32897062235703355164834839 49345593353555032747252259)
  ·
    refine ⟨74018390030332549120878389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49345593353555032747252259 74018390030332549120878389)
    ·
      refine ⟨6939224065343676480082349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74018390030332549120878389 6939224065343676480082349)
      ·
        refine ⟨2602209024503878680030881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6939224065343676480082349 2602209024503878680030881)
        ·
          refine ⟨1951656768377909010023161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2602209024503878680030881 1951656768377909010023161)
          ·
            refine ⟨1463742576283431757517371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951656768377909010023161 1463742576283431757517371)
            ·
              refine ⟨2195613864425147636276057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463742576283431757517371 2195613864425147636276057)
              ·
                refine ⟨1646710398318860727207043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195613864425147636276057 1646710398318860727207043)
                ·
                  refine ⟨2470065597478291090810565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646710398318860727207043 2470065597478291090810565)
                  ·
                    refine ⟨463137299527179579526981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470065597478291090810565 463137299527179579526981)
                    ·
                      rfl

theorem cell22_1352935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1352935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1352935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1352935 prefixEnd_1352935 := by exact prefixLift 1352935
  have htrace : WordTrace (prefixWord ++ tailWord_1352935) baseStart_1352935 baseEnd_1352935 := by
    simpa [prefixWord, tailWord_1352935, baseEnd_1352935] using wordTrace_append hprefix tailTrace_1352935
  have hstable : (prefixWord ++ tailWord_1352935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352935).length < 2 ^ (prefixWord ++ tailWord_1352935).sum := by decide
  have hdescent : baseEnd_1352935 < baseStart_1352935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353004 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1353004 : Nat := 118140960795 + 1353004 * 2 ^ 59
def prefixEnd_1353004 : Nat := 4983230072969 + 3 ^ 40 * 1353004 * 2
def baseEnd_1353004 : Nat := 463160919637286399551769

theorem tailTrace_1353004 : CollatzResearch.WordTrace tailWord_1353004 prefixEnd_1353004 463160919637286399551769 := by
  unfold tailWord_1353004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24674054995152528765757033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32898739993536705021009377 24674054995152528765757033)
  ·
    refine ⟨18505541246364396574317775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24674054995152528765757033 18505541246364396574317775)
    ·
      refine ⟨27758311869546594861476663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18505541246364396574317775 27758311869546594861476663)
      ·
        refine ⟨41637467804319892292214995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27758311869546594861476663 41637467804319892292214995)
        ·
          refine ⟨62456201706479838438322493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41637467804319892292214995 62456201706479838438322493)
          ·
            refine ⟨23421075639929939414370935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62456201706479838438322493 23421075639929939414370935)
            ·
              refine ⟨35131613459894909121556403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23421075639929939414370935 35131613459894909121556403)
              ·
                refine ⟨52697420189842363682334605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35131613459894909121556403 52697420189842363682334605)
                ·
                  refine ⟨19761532571190886380875477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52697420189842363682334605 19761532571190886380875477)
                  ·
                    refine ⟨463160919637286399551769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19761532571190886380875477 463160919637286399551769)
                    ·
                      rfl

theorem cell22_1353004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1353004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353004 prefixEnd_1353004 := by exact prefixLift 1353004
  have htrace : WordTrace (prefixWord ++ tailWord_1353004) baseStart_1353004 baseEnd_1353004 := by
    simpa [prefixWord, tailWord_1353004, baseEnd_1353004] using wordTrace_append hprefix tailTrace_1353004
  have hstable : (prefixWord ++ tailWord_1353004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353004).length < 2 ^ (prefixWord ++ tailWord_1353004).sum := by decide
  have hdescent : baseEnd_1353004 < baseStart_1353004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353010 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_1353010 : Nat := 118140960795 + 1353010 * 2 ^ 59
def prefixEnd_1353010 : Nat := 4983230072969 + 3 ^ 40 * 1353010 * 2
def baseEnd_1353010 : Nat := 463162973559904383901751

theorem tailTrace_1353010 : CollatzResearch.WordTrace tailWord_1353010 prefixEnd_1353010 463162973559904383901751 := by
  unfold tailWord_1353010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337082207070830139058121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32898885885522213704154989 12337082207070830139058121)
  ·
    refine ⟨9252811655303122604293591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12337082207070830139058121 9252811655303122604293591)
    ·
      refine ⟨13879217482954683906440387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9252811655303122604293591 13879217482954683906440387)
      ·
        refine ⟨20818826224432025859660581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13879217482954683906440387 20818826224432025859660581)
        ·
          refine ⟨3903529917081004848686359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20818826224432025859660581 3903529917081004848686359)
          ·
            refine ⟨5855294875621507273029539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903529917081004848686359 5855294875621507273029539)
            ·
              refine ⟨8782942313432260909544309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855294875621507273029539 8782942313432260909544309)
              ·
                refine ⟨823400841884274460269779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8782942313432260909544309 823400841884274460269779)
                ·
                  refine ⟨1235101262826411690404669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823400841884274460269779 1235101262826411690404669)
                  ·
                    refine ⟨463162973559904383901751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235101262826411690404669 463162973559904383901751)
                    ·
                      rfl

theorem cell22_1353010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_1353010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353010 prefixEnd_1353010 := by exact prefixLift 1353010
  have htrace : WordTrace (prefixWord ++ tailWord_1353010) baseStart_1353010 baseEnd_1353010 := by
    simpa [prefixWord, tailWord_1353010, baseEnd_1353010] using wordTrace_append hprefix tailTrace_1353010
  have hstable : (prefixWord ++ tailWord_1353010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353010).length < 2 ^ (prefixWord ++ tailWord_1353010).sum := by decide
  have hdescent : baseEnd_1353010 < baseStart_1353010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353023 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 5]
def baseStart_1353023 : Nat := 118140960795 + 1353023 * 2 ^ 59
def prefixEnd_1353023 : Nat := 4983230072969 + 3 ^ 40 * 1353023 * 2
def baseEnd_1353023 : Nat := 154389141241858894442237

theorem tailTrace_1353023 : CollatzResearch.WordTrace tailWord_1353023 prefixEnd_1353023 154389141241858894442237 := by
  unfold tailWord_1353023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49348802977236223776455723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32899201984824149184303815 49348802977236223776455723)
  ·
    refine ⟨74023204465854335664683585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49348802977236223776455723 74023204465854335664683585)
    ·
      refine ⟨55517403349390751748512689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74023204465854335664683585 55517403349390751748512689)
      ·
        refine ⟨41638052512043063811384517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55517403349390751748512689 41638052512043063811384517)
        ·
          refine ⟨7807134846008074464634597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41638052512043063811384517 7807134846008074464634597)
          ·
            refine ⟨1463837783626513962118987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7807134846008074464634597 1463837783626513962118987)
            ·
              refine ⟨2195756675439770943178481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463837783626513962118987 2195756675439770943178481)
              ·
                refine ⟨1646817506579828207383861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195756675439770943178481 1646817506579828207383861)
                ·
                  refine ⟨154389141241858894442237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1646817506579828207383861 154389141241858894442237)
                  ·
                    rfl

theorem cell22_1353023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].length) (baseStart_1353023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353023 prefixEnd_1353023 := by exact prefixLift 1353023
  have htrace : WordTrace (prefixWord ++ tailWord_1353023) baseStart_1353023 baseEnd_1353023 := by
    simpa [prefixWord, tailWord_1353023, baseEnd_1353023] using wordTrace_append hprefix tailTrace_1353023
  have hstable : (prefixWord ++ tailWord_1353023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353023).length < 2 ^ (prefixWord ++ tailWord_1353023).sum := by decide
  have hdescent : baseEnd_1353023 < baseStart_1353023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353046 : List Nat := [5, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1353046 : Nat := 118140960795 + 1353046 * 2 ^ 59
def prefixEnd_1353046 : Nat := 4983230072969 + 3 ^ 40 * 1353046 * 2
def baseEnd_1353046 : Nat := 51463921899512476666849

theorem tailTrace_1353046 : CollatzResearch.WordTrace tailWord_1353046 prefixEnd_1353046 51463921899512476666849 := by
  unfold tailWord_1353046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084352616009556169033937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32899761237435265803028661 3084352616009556169033937)
  ·
    refine ⟨2313264462007167126775453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3084352616009556169033937 2313264462007167126775453)
    ·
      refine ⟨867474173252687672540795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2313264462007167126775453 867474173252687672540795)
      ·
        refine ⟨1301211259879031508811193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867474173252687672540795 1301211259879031508811193)
        ·
          refine ⟨975908444909273631608395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301211259879031508811193 975908444909273631608395)
          ·
            refine ⟨1463862667363910447412593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975908444909273631608395 1463862667363910447412593)
            ·
              refine ⟨1097897000522932835559445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463862667363910447412593 1097897000522932835559445)
              ·
                refine ⟨51463921899512476666849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097897000522932835559445 51463921899512476666849)
                ·
                  rfl

theorem cell22_1353046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1353046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353046 prefixEnd_1353046 := by exact prefixLift 1353046
  have htrace : WordTrace (prefixWord ++ tailWord_1353046) baseStart_1353046 baseEnd_1353046 := by
    simpa [prefixWord, tailWord_1353046, baseEnd_1353046] using wordTrace_append hprefix tailTrace_1353046
  have hstable : (prefixWord ++ tailWord_1353046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353046).length < 2 ^ (prefixWord ++ tailWord_1353046).sum := by decide
  have hdescent : baseEnd_1353046 < baseStart_1353046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353081 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_1353081 : Nat := 118140960795 + 1353081 * 2 ^ 59
def prefixEnd_1353081 : Nat := 4983230072969 + 3 ^ 40 * 1353081 * 2
def baseEnd_1353081 : Nat := 463187278310883865376533

theorem tailTrace_1353081 : CollatzResearch.WordTrace tailWord_1353081 prefixEnd_1353081 463187278310883865376533 := by
  unfold tailWord_1353081
  simp only [CollatzResearch.WordTrace]
  refine ⟨49350918411026099682067097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32900612274017399788044731 49350918411026099682067097)
  ·
    refine ⟨37013188808269574761550323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49350918411026099682067097 37013188808269574761550323)
    ·
      refine ⟨55519783212404362142325485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37013188808269574761550323 55519783212404362142325485)
      ·
        refine ⟨20819918704651635803372057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55519783212404362142325485 20819918704651635803372057)
        ·
          refine ⟨15614939028488726852529043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20819918704651635803372057 15614939028488726852529043)
          ·
            refine ⟨23422408542733090278793565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15614939028488726852529043 23422408542733090278793565)
            ·
              refine ⟨8783403203524908854547587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23422408542733090278793565 8783403203524908854547587)
              ·
                refine ⟨13175104805287363281821381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783403203524908854547587 13175104805287363281821381)
                ·
                  refine ⟨2470332150991380615341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13175104805287363281821381 2470332150991380615341509)
                  ·
                    refine ⟨463187278310883865376533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470332150991380615341509 463187278310883865376533)
                    ·
                      rfl

theorem cell22_1353081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_1353081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353081 prefixEnd_1353081 := by exact prefixLift 1353081
  have htrace : WordTrace (prefixWord ++ tailWord_1353081) baseStart_1353081 baseEnd_1353081 := by
    simpa [prefixWord, tailWord_1353081, baseEnd_1353081] using wordTrace_append hprefix tailTrace_1353081
  have hstable : (prefixWord ++ tailWord_1353081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353081).length < 2 ^ (prefixWord ++ tailWord_1353081).sum := by decide
  have hdescent : baseEnd_1353081 < baseStart_1353081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353083 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 2, 3]
def baseStart_1353083 : Nat := 118140960795 + 1353083 * 2 ^ 59
def prefixEnd_1353083 : Nat := 4983230072969 + 3 ^ 40 * 1353083 * 2
def baseEnd_1353083 : Nat := 463187962951756526826527

theorem tailTrace_1353083 : CollatzResearch.WordTrace tailWord_1353083 prefixEnd_1353083 463187962951756526826527 := by
  unfold tailWord_1353083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49350991357018854023639903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32900660904679236015759935 49350991357018854023639903)
  ·
    refine ⟨74026487035528281035459855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49350991357018854023639903 74026487035528281035459855)
    ·
      refine ⟨111039730553292421553189783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74026487035528281035459855 111039730553292421553189783)
      ·
        refine ⟨166559595829938632329784675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111039730553292421553189783 166559595829938632329784675)
        ·
          refine ⟨249839393744907948494677013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166559595829938632329784675 249839393744907948494677013)
          ·
            refine ⟨11711221581792560085687985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249839393744907948494677013 11711221581792560085687985)
            ·
              refine ⟨8783416186344420064265989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11711221581792560085687985 8783416186344420064265989)
              ·
                refine ⟨1646890534939578762049873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8783416186344420064265989 1646890534939578762049873)
                ·
                  refine ⟨1235167901204684071537405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646890534939578762049873 1235167901204684071537405)
                  ·
                    refine ⟨463187962951756526826527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235167901204684071537405 463187962951756526826527)
                    ·
                      rfl

theorem cell22_1353083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].length) (baseStart_1353083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353083 prefixEnd_1353083 := by exact prefixLift 1353083
  have htrace : WordTrace (prefixWord ++ tailWord_1353083) baseStart_1353083 baseEnd_1353083 := by
    simpa [prefixWord, tailWord_1353083, baseEnd_1353083] using wordTrace_append hprefix tailTrace_1353083
  have hstable : (prefixWord ++ tailWord_1353083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353083).length < 2 ^ (prefixWord ++ tailWord_1353083).sum := by decide
  have hdescent : baseEnd_1353083 < baseStart_1353083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353085 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1353085 : Nat := 118140960795 + 1353085 * 2 ^ 59
def prefixEnd_1353085 : Nat := 4983230072969 + 3 ^ 40 * 1353085 * 2
def baseEnd_1353085 : Nat := 154396215864209729425507

theorem tailTrace_1353085 : CollatzResearch.WordTrace tailWord_1353085 prefixEnd_1353085 154396215864209729425507 := by
  unfold tailWord_1353085
  simp only [CollatzResearch.WordTrace]
  refine ⟨49351064303011608365212709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32900709535341072243475139 49351064303011608365212709)
  ·
    refine ⟨9253324556814676568477383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49351064303011608365212709 9253324556814676568477383)
    ·
      refine ⟨13879986835222014852716075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253324556814676568477383 13879986835222014852716075)
      ·
        refine ⟨20819980252833022279074113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13879986835222014852716075 20819980252833022279074113)
        ·
          refine ⟨15614985189624766709305585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20819980252833022279074113 15614985189624766709305585)
          ·
            refine ⟨11711238892218575031979189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15614985189624766709305585 11711238892218575031979189)
            ·
              refine ⟨1097928646145491409248049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11711238892218575031979189 1097928646145491409248049)
              ·
                refine ⟨823446484609118556936037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097928646145491409248049 823446484609118556936037)
                ·
                  refine ⟨154396215864209729425507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823446484609118556936037 154396215864209729425507)
                  ·
                    rfl

theorem cell22_1353085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1353085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353085 prefixEnd_1353085 := by exact prefixLift 1353085
  have htrace : WordTrace (prefixWord ++ tailWord_1353085) baseStart_1353085 baseEnd_1353085 := by
    simpa [prefixWord, tailWord_1353085, baseEnd_1353085] using wordTrace_append hprefix tailTrace_1353085
  have hstable : (prefixWord ++ tailWord_1353085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353085).length < 2 ^ (prefixWord ++ tailWord_1353085).sum := by decide
  have hdescent : baseEnd_1353085 < baseStart_1353085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353096 : List Nat := [2, 1, 3, 3, 1, 2, 1, 9]
def baseStart_1353096 : Nat := 118140960795 + 1353096 * 2 ^ 59
def prefixEnd_1353096 : Nat := 4983230072969 + 3 ^ 40 * 1353096 * 2
def baseEnd_1353096 : Nat := 51465823679714314027943

theorem tailTrace_1353096 : CollatzResearch.WordTrace tailWord_1353096 prefixEnd_1353096 51465823679714314027943 := by
  unfold tailWord_1353096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675732752985878621931571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32900977003981171495908761 24675732752985878621931571)
  ·
    refine ⟨37013599129478817932897357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24675732752985878621931571 37013599129478817932897357)
    ·
      refine ⟨13880099673554556724836509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37013599129478817932897357 13880099673554556724836509)
      ·
        refine ⟨5205037377582958771813691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13880099673554556724836509 5205037377582958771813691)
        ·
          refine ⟨7807556066374438157720537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205037377582958771813691 7807556066374438157720537)
          ·
            refine ⟨5855667049780828618290403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7807556066374438157720537 5855667049780828618290403)
            ·
              refine ⟨8783500574671242927435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855667049780828618290403 8783500574671242927435605)
              ·
                refine ⟨51465823679714314027943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8783500574671242927435605 51465823679714314027943)
                ·
                  rfl

theorem cell22_1353096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_1353096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353096 prefixEnd_1353096 := by exact prefixLift 1353096
  have htrace : WordTrace (prefixWord ++ tailWord_1353096) baseStart_1353096 baseEnd_1353096 := by
    simpa [prefixWord, tailWord_1353096, baseEnd_1353096] using wordTrace_append hprefix tailTrace_1353096
  have hstable : (prefixWord ++ tailWord_1353096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353096).length < 2 ^ (prefixWord ++ tailWord_1353096).sum := by decide
  have hdescent : baseEnd_1353096 < baseStart_1353096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353233 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_1353233 : Nat := 118140960795 + 1353233 * 2 ^ 59
def prefixEnd_1353233 : Nat := 4983230072969 + 3 ^ 40 * 1353233 * 2
def baseEnd_1353233 : Nat := 463239311017206135576067

theorem tailTrace_1353233 : CollatzResearch.WordTrace tailWord_1353233 prefixEnd_1353233 463239311017206135576067 := by
  unfold tailWord_1353233
  simp only [CollatzResearch.WordTrace]
  refine ⟨49356462306475429641600353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32904308204316953094400235 49356462306475429641600353)
  ·
    refine ⟨37017346729856572231200265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49356462306475429641600353 37017346729856572231200265)
    ·
      refine ⟨27763010047392429173400199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37017346729856572231200265 27763010047392429173400199)
      ·
        refine ⟨41644515071088643760100299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763010047392429173400199 41644515071088643760100299)
        ·
          refine ⟨62466772606632965640150449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41644515071088643760100299 62466772606632965640150449)
          ·
            refine ⟨46850079454974724230112837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62466772606632965640150449 46850079454974724230112837)
            ·
              refine ⟨8784389897807760793146157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46850079454974724230112837 8784389897807760793146157)
              ·
                refine ⟨3294146211677910297429809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8784389897807760793146157 3294146211677910297429809)
                ·
                  refine ⟨2470609658758432723072357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294146211677910297429809 2470609658758432723072357)
                  ·
                    refine ⟨463239311017206135576067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470609658758432723072357 463239311017206135576067)
                    ·
                      rfl

theorem cell22_1353233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_1353233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353233 prefixEnd_1353233 := by exact prefixLift 1353233
  have htrace : WordTrace (prefixWord ++ tailWord_1353233) baseStart_1353233 baseEnd_1353233 := by
    simpa [prefixWord, tailWord_1353233, baseEnd_1353233] using wordTrace_append hprefix tailTrace_1353233
  have hstable : (prefixWord ++ tailWord_1353233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353233).length < 2 ^ (prefixWord ++ tailWord_1353233).sum := by decide
  have hdescent : baseEnd_1353233 < baseStart_1353233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353237 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 4]
def baseStart_1353237 : Nat := 118140960795 + 1353237 * 2 ^ 59
def prefixEnd_1353237 : Nat := 4983230072969 + 3 ^ 40 * 1353237 * 2
def baseEnd_1353237 : Nat := 154413560099650486158685

theorem tailTrace_1353237 : CollatzResearch.WordTrace tailWord_1353237 prefixEnd_1353237 154413560099650486158685 := by
  unfold tailWord_1353237
  simp only [CollatzResearch.WordTrace]
  refine ⟨49356608198460938324745965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32904405465640625549830643 49356608198460938324745965)
  ·
    refine ⟨18508728074422851871779737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49356608198460938324745965 18508728074422851871779737)
    ·
      refine ⟨13881546055817138903834803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18508728074422851871779737 13881546055817138903834803)
      ·
        refine ⟨20822319083725708355752205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13881546055817138903834803 20822319083725708355752205)
        ·
          refine ⟨7808369656397140633407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20822319083725708355752205 7808369656397140633407077)
          ·
            refine ⟨1464069310574463868763827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7808369656397140633407077 1464069310574463868763827)
            ·
              refine ⟨2196103965861695803145741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464069310574463868763827 2196103965861695803145741)
              ·
                refine ⟨823538987198135926179653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2196103965861695803145741 823538987198135926179653)
                ·
                  refine ⟨154413560099650486158685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823538987198135926179653 154413560099650486158685)
                  ·
                    rfl

theorem cell22_1353237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_1353237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353237 prefixEnd_1353237 := by exact prefixLift 1353237
  have htrace : WordTrace (prefixWord ++ tailWord_1353237) baseStart_1353237 baseEnd_1353237 := by
    simpa [prefixWord, tailWord_1353237, baseEnd_1353237] using wordTrace_append hprefix tailTrace_1353237
  have hstable : (prefixWord ++ tailWord_1353237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353237).length < 2 ^ (prefixWord ++ tailWord_1353237).sum := by decide
  have hdescent : baseEnd_1353237 < baseStart_1353237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353248 : List Nat := [2, 1, 1, 6, 1, 1, 10]
def baseStart_1353248 : Nat := 118140960795 + 1353248 * 2 ^ 59
def prefixEnd_1353248 : Nat := 4983230072969 + 3 ^ 40 * 1353248 * 2
def baseEnd_1353248 : Nat := 17157201697175966535223

theorem tailTrace_1353248 : CollatzResearch.WordTrace tailWord_1353248 prefixEnd_1353248 17157201697175966535223 := by
  unfold tailWord_1353248
  simp only [CollatzResearch.WordTrace]
  refine ⟨24678504700710543601698199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32904672934280724802264265 24678504700710543601698199)
  ·
    refine ⟨37017757051065815402547299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24678504700710543601698199 37017757051065815402547299)
    ·
      refine ⟨55526635576598723103820949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37017757051065815402547299 55526635576598723103820949)
      ·
        refine ⟨2602811042653065145491607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55526635576598723103820949 2602811042653065145491607)
        ·
          refine ⟨3904216563979597718237411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602811042653065145491607 3904216563979597718237411)
          ·
            refine ⟨5856324845969396577356117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904216563979597718237411 5856324845969396577356117)
            ·
              refine ⟨17157201697175966535223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5856324845969396577356117 17157201697175966535223)
              ·
                rfl

theorem cell22_1353248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 10].length) (baseStart_1353248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353248 prefixEnd_1353248 := by exact prefixLift 1353248
  have htrace : WordTrace (prefixWord ++ tailWord_1353248) baseStart_1353248 baseEnd_1353248 := by
    simpa [prefixWord, tailWord_1353248, baseEnd_1353248] using wordTrace_append hprefix tailTrace_1353248
  have hstable : (prefixWord ++ tailWord_1353248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353248).length < 2 ^ (prefixWord ++ tailWord_1353248).sum := by decide
  have hdescent : baseEnd_1353248 < baseStart_1353248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353269 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1353269 : Nat := 118140960795 + 1353269 * 2 ^ 59
def prefixEnd_1353269 : Nat := 4983230072969 + 3 ^ 40 * 1353269 * 2
def baseEnd_1353269 : Nat := 463251634552914041675957

theorem tailTrace_1353269 : CollatzResearch.WordTrace tailWord_1353269 prefixEnd_1353269 463251634552914041675957 := by
  unfold tailWord_1353269
  simp only [CollatzResearch.WordTrace]
  refine ⟨49357775334345007789910861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32905183556230005193273907 49357775334345007789910861)
  ·
    refine ⟨18509165750379377921216573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49357775334345007789910861 18509165750379377921216573)
    ·
      refine ⟨6940937156392266720456215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18509165750379377921216573 6940937156392266720456215)
      ·
        refine ⟨10411405734588400080684323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940937156392266720456215 10411405734588400080684323)
        ·
          refine ⟨15617108601882600121026485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10411405734588400080684323 15617108601882600121026485)
          ·
            refine ⟨1464103931426493761346233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15617108601882600121026485 1464103931426493761346233)
            ·
              refine ⟨1098077948569870321009675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464103931426493761346233 1098077948569870321009675)
              ·
                refine ⟨1647116922854805481514513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098077948569870321009675 1647116922854805481514513)
                ·
                  refine ⟨1235337692141104111135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647116922854805481514513 1235337692141104111135885)
                  ·
                    refine ⟨463251634552914041675957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235337692141104111135885 463251634552914041675957)
                    ·
                      rfl

theorem cell22_1353269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1353269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353269 prefixEnd_1353269 := by exact prefixLift 1353269
  have htrace : WordTrace (prefixWord ++ tailWord_1353269) baseStart_1353269 baseEnd_1353269 := by
    simpa [prefixWord, tailWord_1353269, baseEnd_1353269] using wordTrace_append hprefix tailTrace_1353269
  have hstable : (prefixWord ++ tailWord_1353269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353269).length < 2 ^ (prefixWord ++ tailWord_1353269).sum := by decide
  have hdescent : baseEnd_1353269 < baseStart_1353269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353297 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1353297 : Nat := 118140960795 + 1353297 * 2 ^ 59
def prefixEnd_1353297 : Nat := 4983230072969 + 3 ^ 40 * 1353297 * 2
def baseEnd_1353297 : Nat := 463261219525131301975871

theorem tailTrace_1353297 : CollatzResearch.WordTrace tailWord_1353297 prefixEnd_1353297 463261219525131301975871 := by
  unfold tailWord_1353297
  simp only [CollatzResearch.WordTrace]
  refine ⟨49358796578243568571930145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32905864385495712381286763 49358796578243568571930145)
  ·
    refine ⟨37019097433682676428947609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49358796578243568571930145 37019097433682676428947609)
    ·
      refine ⟨27764323075262007321710707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37019097433682676428947609 27764323075262007321710707)
      ·
        refine ⟨41646484612893010982566061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27764323075262007321710707 41646484612893010982566061)
        ·
          refine ⟨15617431729834879118462273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41646484612893010982566061 15617431729834879118462273)
          ·
            refine ⟨11713073797376159338846705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15617431729834879118462273 11713073797376159338846705)
            ·
              refine ⟨8784805348032119504135029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11713073797376159338846705 8784805348032119504135029)
              ·
                refine ⟨823575501378011203512659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8784805348032119504135029 823575501378011203512659)
                ·
                  refine ⟨1235363252067016805268989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823575501378011203512659 1235363252067016805268989)
                  ·
                    refine ⟨463261219525131301975871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235363252067016805268989 463261219525131301975871)
                    ·
                      rfl

theorem cell22_1353297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1353297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353297 prefixEnd_1353297 := by exact prefixLift 1353297
  have htrace : WordTrace (prefixWord ++ tailWord_1353297) baseStart_1353297 baseEnd_1353297 := by
    simpa [prefixWord, tailWord_1353297, baseEnd_1353297] using wordTrace_append hprefix tailTrace_1353297
  have hstable : (prefixWord ++ tailWord_1353297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353297).length < 2 ^ (prefixWord ++ tailWord_1353297).sum := by decide
  have hdescent : baseEnd_1353297 < baseStart_1353297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353340 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1353340 : Nat := 118140960795 + 1353340 * 2 ^ 59
def prefixEnd_1353340 : Nat := 4983230072969 + 3 ^ 40 * 1353340 * 2
def baseEnd_1353340 : Nat := 463275939303893523150739

theorem tailTrace_1353340 : CollatzResearch.WordTrace tailWord_1353340 prefixEnd_1353340 463275939303893523150739 := by
  unfold tailWord_1353340
  simp only [CollatzResearch.WordTrace]
  refine ⟨24680182458543893457872737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32906909944725191277163649 24680182458543893457872737)
  ·
    refine ⟨18510136843907920093404553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24680182458543893457872737 18510136843907920093404553)
    ·
      refine ⟨13882602632930940070053415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18510136843907920093404553 13882602632930940070053415)
      ·
        refine ⟨20823903949396410105080123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882602632930940070053415 20823903949396410105080123)
        ·
          refine ⟨31235855924094615157620185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20823903949396410105080123 31235855924094615157620185)
          ·
            refine ⟨23426891943070961368215139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31235855924094615157620185 23426891943070961368215139)
            ·
              refine ⟨35140337914606442052322709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23426891943070961368215139 35140337914606442052322709)
              ·
                refine ⟨1647203339747176971202627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35140337914606442052322709 1647203339747176971202627)
                ·
                  refine ⟨2470805009620765456803941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647203339747176971202627 2470805009620765456803941)
                  ·
                    refine ⟨463275939303893523150739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470805009620765456803941 463275939303893523150739)
                    ·
                      rfl

theorem cell22_1353340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1353340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353340 prefixEnd_1353340 := by exact prefixLift 1353340
  have htrace : WordTrace (prefixWord ++ tailWord_1353340) baseStart_1353340 baseEnd_1353340 := by
    simpa [prefixWord, tailWord_1353340, baseEnd_1353340] using wordTrace_append hprefix tailTrace_1353340
  have hstable : (prefixWord ++ tailWord_1353340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353340).length < 2 ^ (prefixWord ++ tailWord_1353340).sum := by decide
  have hdescent : baseEnd_1353340 < baseStart_1353340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353372 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_1353372 : Nat := 118140960795 + 1353372 * 2 ^ 59
def prefixEnd_1353372 : Nat := 4983230072969 + 3 ^ 40 * 1353372 * 2
def baseEnd_1353372 : Nat := 154428964519285368783547

theorem tailTrace_1353372 : CollatzResearch.WordTrace tailWord_1353372 prefixEnd_1353372 154428964519285368783547 := by
  unfold tailWord_1353372
  simp only [CollatzResearch.WordTrace]
  refine ⟨24680766026485928190455185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32907688035314570920606913 24680766026485928190455185)
  ·
    refine ⟨18510574519864446142841389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24680766026485928190455185 18510574519864446142841389)
    ·
      refine ⟨6941465444949167303565521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18510574519864446142841389 6941465444949167303565521)
      ·
        refine ⟨5206099083711875477674141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6941465444949167303565521 5206099083711875477674141)
        ·
          refine ⟨1952287156391953304127803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5206099083711875477674141 1952287156391953304127803)
          ·
            refine ⟨2928430734587929956191705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952287156391953304127803 2928430734587929956191705)
            ·
              refine ⟨2196323050940947467143779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2928430734587929956191705 2196323050940947467143779)
              ·
                refine ⟨3294484576411421200715669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196323050940947467143779 3294484576411421200715669)
                ·
                  refine ⟨154428964519285368783547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3294484576411421200715669 154428964519285368783547)
                  ·
                    rfl

theorem cell22_1353372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_1353372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353372 prefixEnd_1353372 := by exact prefixLift 1353372
  have htrace : WordTrace (prefixWord ++ tailWord_1353372) baseStart_1353372 baseEnd_1353372 := by
    simpa [prefixWord, tailWord_1353372, baseEnd_1353372] using wordTrace_append hprefix tailTrace_1353372
  have hstable : (prefixWord ++ tailWord_1353372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353372).length < 2 ^ (prefixWord ++ tailWord_1353372).sum := by decide
  have hdescent : baseEnd_1353372 < baseStart_1353372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353479 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 5]
def baseStart_1353479 : Nat := 118140960795 + 1353479 * 2 ^ 59
def prefixEnd_1353479 : Nat := 4983230072969 + 3 ^ 40 * 1353479 * 2
def baseEnd_1353479 : Nat := 154441173948181164641771

theorem tailTrace_1353479 : CollatzResearch.WordTrace tailWord_1353479 prefixEnd_1353479 154441173948181164641771 := by
  unfold tailWord_1353479
  simp only [CollatzResearch.WordTrace]
  refine ⟨49365434663584213655055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32910289775722809103370327 49365434663584213655055491)
  ·
    refine ⟨74048151995376320482583237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49365434663584213655055491 74048151995376320482583237)
    ·
      refine ⟨13884028499133060090484357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74048151995376320482583237 13884028499133060090484357)
      ·
        refine ⟨2603255343587448766965817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13884028499133060090484357 2603255343587448766965817)
        ·
          refine ⟨1952441507690586575224363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2603255343587448766965817 1952441507690586575224363)
          ·
            refine ⟨2928662261535879862836545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952441507690586575224363 2928662261535879862836545)
            ·
              refine ⟨2196496696151909897127409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2928662261535879862836545 2196496696151909897127409)
              ·
                refine ⟨1647372522113932422845557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196496696151909897127409 1647372522113932422845557)
                ·
                  refine ⟨154441173948181164641771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647372522113932422845557 154441173948181164641771)
                  ·
                    rfl

theorem cell22_1353479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].length) (baseStart_1353479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353479 prefixEnd_1353479 := by exact prefixLift 1353479
  have htrace : WordTrace (prefixWord ++ tailWord_1353479) baseStart_1353479 baseEnd_1353479 := by
    simpa [prefixWord, tailWord_1353479, baseEnd_1353479] using wordTrace_append hprefix tailTrace_1353479
  have hstable : (prefixWord ++ tailWord_1353479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353479).length < 2 ^ (prefixWord ++ tailWord_1353479).sum := by decide
  have hdescent : baseEnd_1353479 < baseStart_1353479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353485 : List Nat := [1, 7, 2, 1, 2, 1, 1, 7]
def baseStart_1353485 : Nat := 118140960795 + 1353485 * 2 ^ 59
def prefixEnd_1353485 : Nat := 4983230072969 + 3 ^ 40 * 1353485 * 2
def baseEnd_1353485 : Nat := 51480619529684608697255

theorem tailTrace_1353485 : CollatzResearch.WordTrace tailWord_1353485 prefixEnd_1353485 51480619529684608697255 := by
  unfold tailWord_1353485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49365653501562476679773909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32910435667708317786515939 49365653501562476679773909)
  ·
    refine ⟨1157007503942870547182201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49365653501562476679773909 1157007503942870547182201)
    ·
      refine ⟨867755627957152910386651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1157007503942870547182201 867755627957152910386651)
      ·
        refine ⟨1301633441935729365579977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867755627957152910386651 1301633441935729365579977)
        ·
          refine ⟨976225081451797024184983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301633441935729365579977 976225081451797024184983)
          ·
            refine ⟨1464337622177695536277475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976225081451797024184983 1464337622177695536277475)
            ·
              refine ⟨2196506433266543304416213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464337622177695536277475 2196506433266543304416213)
              ·
                refine ⟨51480619529684608697255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2196506433266543304416213 51480619529684608697255)
                ·
                  rfl

theorem cell22_1353485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 7].length) (baseStart_1353485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353485 prefixEnd_1353485 := by exact prefixLift 1353485
  have htrace : WordTrace (prefixWord ++ tailWord_1353485) baseStart_1353485 baseEnd_1353485 := by
    simpa [prefixWord, tailWord_1353485, baseEnd_1353485] using wordTrace_append hprefix tailTrace_1353485
  have hstable : (prefixWord ++ tailWord_1353485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353485).length < 2 ^ (prefixWord ++ tailWord_1353485).sum := by decide
  have hdescent : baseEnd_1353485 < baseStart_1353485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353522 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1353522 : Nat := 118140960795 + 1353522 * 2 ^ 59
def prefixEnd_1353522 : Nat := 4983230072969 + 3 ^ 40 * 1353522 * 2
def baseEnd_1353522 : Nat := 463338241623305715100181

theorem tailTrace_1353522 : CollatzResearch.WordTrace tailWord_1353522 prefixEnd_1353522 463338241623305715100181 := by
  unfold tailWord_1353522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341750750607107999717705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32911335334952287999247213 12341750750607107999717705)
  ·
    refine ⟨9256313062955330999788279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12341750750607107999717705 9256313062955330999788279)
    ·
      refine ⟨13884469594432996499682419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9256313062955330999788279 13884469594432996499682419)
      ·
        refine ⟨20826704391649494749523629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13884469594432996499682419 20826704391649494749523629)
        ·
          refine ⟨7810014146868560531071361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20826704391649494749523629 7810014146868560531071361)
          ·
            refine ⟨5857510610151420398303521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7810014146868560531071361 5857510610151420398303521)
            ·
              refine ⟨4393132957613565298727641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5857510610151420398303521 4393132957613565298727641)
              ·
                refine ⟨3294849718210173974045731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4393132957613565298727641 3294849718210173974045731)
                ·
                  refine ⟨4942274577315260961068597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294849718210173974045731 4942274577315260961068597)
                  ·
                    refine ⟨463338241623305715100181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4942274577315260961068597 463338241623305715100181)
                    ·
                      rfl

theorem cell22_1353522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1353522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353522 prefixEnd_1353522 := by exact prefixLift 1353522
  have htrace : WordTrace (prefixWord ++ tailWord_1353522) baseStart_1353522 baseEnd_1353522 := by
    simpa [prefixWord, tailWord_1353522, baseEnd_1353522] using wordTrace_append hprefix tailTrace_1353522
  have hstable : (prefixWord ++ tailWord_1353522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353522).length < 2 ^ (prefixWord ++ tailWord_1353522).sum := by decide
  have hdescent : baseEnd_1353522 < baseStart_1353522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353526 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1353526 : Nat := 118140960795 + 1353526 * 2 ^ 59
def prefixEnd_1353526 : Nat := 4983230072969 + 3 ^ 40 * 1353526 * 2
def baseEnd_1353526 : Nat := 463339610905051038000169

theorem tailTrace_1353526 : CollatzResearch.WordTrace tailWord_1353526 prefixEnd_1353526 463339610905051038000169 := by
  unfold tailWord_1353526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085446805900871292626027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32911432596275960454677621 3085446805900871292626027)
  ·
    refine ⟨4628170208851306938939041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085446805900871292626027 4628170208851306938939041)
    ·
      refine ⟨3471127656638480204204281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4628170208851306938939041 3471127656638480204204281)
      ·
        refine ⟨2603345742478860153153211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471127656638480204204281 2603345742478860153153211)
        ·
          refine ⟨3905018613718290229729817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603345742478860153153211 3905018613718290229729817)
          ·
            refine ⟨2928763960288717672297363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3905018613718290229729817 2928763960288717672297363)
            ·
              refine ⟨4393145940433076508446045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928763960288717672297363 4393145940433076508446045)
              ·
                refine ⟨1647429727662403690667267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393145940433076508446045 1647429727662403690667267)
                ·
                  refine ⟨2471144591493605536000901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647429727662403690667267 2471144591493605536000901)
                  ·
                    refine ⟨463339610905051038000169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471144591493605536000901 463339610905051038000169)
                    ·
                      rfl

theorem cell22_1353526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1353526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353526 prefixEnd_1353526 := by exact prefixLift 1353526
  have htrace : WordTrace (prefixWord ++ tailWord_1353526) baseStart_1353526 baseEnd_1353526 := by
    simpa [prefixWord, tailWord_1353526, baseEnd_1353526] using wordTrace_append hprefix tailTrace_1353526
  have hstable : (prefixWord ++ tailWord_1353526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353526).length < 2 ^ (prefixWord ++ tailWord_1353526).sum := by decide
  have hdescent : baseEnd_1353526 < baseStart_1353526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353539 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 2, 3]
def baseStart_1353539 : Nat := 118140960795 + 1353539 * 2 ^ 59
def prefixEnd_1353539 : Nat := 4983230072969 + 3 ^ 40 * 1353539 * 2
def baseEnd_1353539 : Nat := 463344061070723337425129

theorem tailTrace_1353539 : CollatzResearch.WordTrace tailWord_1353539 prefixEnd_1353539 463344061070723337425129 := by
  unfold tailWord_1353539
  simp only [CollatzResearch.WordTrace]
  refine ⟨49367623043366843902239671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32911748695577895934826447 49367623043366843902239671)
  ·
    refine ⟨74051434565050265853359507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49367623043366843902239671 74051434565050265853359507)
    ·
      refine ⟨111077151847575398780039261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74051434565050265853359507 111077151847575398780039261)
      ·
        refine ⟨41653931942840774542514723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111077151847575398780039261 41653931942840774542514723)
        ·
          refine ⟨62480897914261161813772085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41653931942840774542514723 62480897914261161813772085)
          ·
            refine ⟨5857584179461983920041133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62480897914261161813772085 5857584179461983920041133)
            ·
              refine ⟨2196594067298243970015425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5857584179461983920041133 2196594067298243970015425)
              ·
                refine ⟨1647445550473682977511569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196594067298243970015425 1647445550473682977511569)
                ·
                  refine ⟨1235584162855262233133677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647445550473682977511569 1235584162855262233133677)
                  ·
                    refine ⟨463344061070723337425129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235584162855262233133677 463344061070723337425129)
                    ·
                      rfl

theorem cell22_1353539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].length) (baseStart_1353539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353539 prefixEnd_1353539 := by exact prefixLift 1353539
  have htrace : WordTrace (prefixWord ++ tailWord_1353539) baseStart_1353539 baseEnd_1353539 := by
    simpa [prefixWord, tailWord_1353539, baseEnd_1353539] using wordTrace_append hprefix tailTrace_1353539
  have hstable : (prefixWord ++ tailWord_1353539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353539).length < 2 ^ (prefixWord ++ tailWord_1353539).sum := by decide
  have hdescent : baseEnd_1353539 < baseStart_1353539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353597 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1353597 : Nat := 118140960795 + 1353597 * 2 ^ 59
def prefixEnd_1353597 : Nat := 4983230072969 + 3 ^ 40 * 1353597 * 2
def baseEnd_1353597 : Nat := 154454638552010173158317

theorem tailTrace_1353597 : CollatzResearch.WordTrace tailWord_1353597 prefixEnd_1353597 154454638552010173158317 := by
  unfold tailWord_1353597
  simp only [CollatzResearch.WordTrace]
  refine ⟨49369738477156719807851045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32913158984771146538567363 49369738477156719807851045)
  ·
    refine ⟨9256825964466884963972071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49369738477156719807851045 9256825964466884963972071)
    ·
      refine ⟨13885238946700327445958107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9256825964466884963972071 13885238946700327445958107)
      ·
        refine ⟨20827858420050491168937161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885238946700327445958107 20827858420050491168937161)
        ·
          refine ⟨15620893815037868376702871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827858420050491168937161 15620893815037868376702871)
          ·
            refine ⟨23431340722556802565054307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620893815037868376702871 23431340722556802565054307)
            ·
              refine ⟨35147011083835203847581461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23431340722556802565054307 35147011083835203847581461)
              ·
                refine ⟨1647516144554775180355381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35147011083835203847581461 1647516144554775180355381)
                ·
                  refine ⟨154454638552010173158317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647516144554775180355381 154454638552010173158317)
                  ·
                    rfl

theorem cell22_1353597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1353597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353597 prefixEnd_1353597 := by exact prefixLift 1353597
  have htrace : WordTrace (prefixWord ++ tailWord_1353597) baseStart_1353597 baseEnd_1353597 := by
    simpa [prefixWord, tailWord_1353597, baseEnd_1353597] using wordTrace_append hprefix tailTrace_1353597
  have hstable : (prefixWord ++ tailWord_1353597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353597).length < 2 ^ (prefixWord ++ tailWord_1353597).sum := by decide
  have hdescent : baseEnd_1353597 < baseStart_1353597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353657 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_1353657 : Nat := 118140960795 + 1353657 * 2 ^ 59
def prefixEnd_1353657 : Nat := 4983230072969 + 3 ^ 40 * 1353657 * 2
def baseEnd_1353657 : Nat := 463384454882210362974767

theorem tailTrace_1353657 : CollatzResearch.WordTrace tailWord_1353657 prefixEnd_1353657 463384454882210362974767 := by
  unfold tailWord_1353657
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371926856939350055035225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32914617904626233370023483 49371926856939350055035225)
  ·
    refine ⟨37028945142704512541276419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49371926856939350055035225 37028945142704512541276419)
    ·
      refine ⟨55543417714056768811914629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37028945142704512541276419 55543417714056768811914629)
      ·
        refine ⟨10414390821385644152233993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55543417714056768811914629 10414390821385644152233993)
        ·
          refine ⟨7810793116039233114175495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10414390821385644152233993 7810793116039233114175495)
          ·
            refine ⟨11716189674058849671263243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7810793116039233114175495 11716189674058849671263243)
            ·
              refine ⟨17574284511088274506894865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11716189674058849671263243 17574284511088274506894865)
              ·
                refine ⟨13180713383316205880171149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17574284511088274506894865 13180713383316205880171149)
                ·
                  refine ⟨4942767518743577205064181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13180713383316205880171149 4942767518743577205064181)
                  ·
                    refine ⟨463384454882210362974767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4942767518743577205064181 463384454882210362974767)
                    ·
                      rfl

theorem cell22_1353657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_1353657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353657 prefixEnd_1353657 := by exact prefixLift 1353657
  have htrace : WordTrace (prefixWord ++ tailWord_1353657) baseStart_1353657 baseEnd_1353657 := by
    simpa [prefixWord, tailWord_1353657, baseEnd_1353657] using wordTrace_append hprefix tailTrace_1353657
  have hstable : (prefixWord ++ tailWord_1353657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353657).length < 2 ^ (prefixWord ++ tailWord_1353657).sum := by decide
  have hdescent : baseEnd_1353657 < baseStart_1353657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353689 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_1353689 : Nat := 118140960795 + 1353689 * 2 ^ 59
def prefixEnd_1353689 : Nat := 4983230072969 + 3 ^ 40 * 1353689 * 2
def baseEnd_1353689 : Nat := 463395409136172946174669

theorem tailTrace_1353689 : CollatzResearch.WordTrace tailWord_1353689 prefixEnd_1353689 463395409136172946174669 := by
  unfold tailWord_1353689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49373093992823419520200121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32915395995215613013466747 49373093992823419520200121)
  ·
    refine ⟨37029820494617564640150091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49373093992823419520200121 37029820494617564640150091)
    ·
      refine ⟨55544730741926346960225137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37029820494617564640150091 55544730741926346960225137)
      ·
        refine ⟨41658548056444760220168853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55544730741926346960225137 41658548056444760220168853)
        ·
          refine ⟨1952744440145848135320415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41658548056444760220168853 1952744440145848135320415)
          ·
            refine ⟨2929116660218772202980623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952744440145848135320415 2929116660218772202980623)
            ·
              refine ⟨4393674990328158304470935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929116660218772202980623 4393674990328158304470935)
              ·
                refine ⟨6590512485492237456706403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393674990328158304470935 6590512485492237456706403)
                ·
                  refine ⟨9885768728238356185059605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590512485492237456706403 9885768728238356185059605)
                  ·
                    refine ⟨463395409136172946174669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9885768728238356185059605 463395409136172946174669)
                    ·
                      rfl

theorem cell22_1353689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_1353689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353689 prefixEnd_1353689 := by exact prefixLift 1353689
  have htrace : WordTrace (prefixWord ++ tailWord_1353689) baseStart_1353689 baseEnd_1353689 := by
    simpa [prefixWord, tailWord_1353689, baseEnd_1353689] using wordTrace_append hprefix tailTrace_1353689
  have hstable : (prefixWord ++ tailWord_1353689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353689).length < 2 ^ (prefixWord ++ tailWord_1353689).sum := by decide
  have hdescent : baseEnd_1353689 < baseStart_1353689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353693 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1353693 : Nat := 118140960795 + 1353693 * 2 ^ 59
def prefixEnd_1353693 : Nat := 4983230072969 + 3 ^ 40 * 1353693 * 2
def baseEnd_1353693 : Nat := 154465592805972756358219

theorem tailTrace_1353693 : CollatzResearch.WordTrace tailWord_1353693 prefixEnd_1353693 154465592805972756358219 := by
  unfold tailWord_1353693
  simp only [CollatzResearch.WordTrace]
  refine ⟨49373239884808928203345733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32915493256539285468897155 49373239884808928203345733)
  ·
    refine ⟨9257482478401674038127325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49373239884808928203345733 9257482478401674038127325)
    ·
      refine ⟨3471555929400627764297747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9257482478401674038127325 3471555929400627764297747)
      ·
        refine ⟨5207333894100941646446621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471555929400627764297747 5207333894100941646446621)
        ·
          refine ⟨1952750210287853117417483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5207333894100941646446621 1952750210287853117417483)
          ·
            refine ⟨2929125315431779676126225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952750210287853117417483 2929125315431779676126225)
            ·
              refine ⟨2196843986573834757094669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929125315431779676126225 2196843986573834757094669)
              ·
                refine ⟨823816494965188033910501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2196843986573834757094669 823816494965188033910501)
                ·
                  refine ⟨154465592805972756358219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823816494965188033910501 154465592805972756358219)
                  ·
                    rfl

theorem cell22_1353693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1353693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353693 prefixEnd_1353693 := by exact prefixLift 1353693
  have htrace : WordTrace (prefixWord ++ tailWord_1353693) baseStart_1353693 baseEnd_1353693 := by
    simpa [prefixWord, tailWord_1353693, baseEnd_1353693] using wordTrace_append hprefix tailTrace_1353693
  have hstable : (prefixWord ++ tailWord_1353693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353693).length < 2 ^ (prefixWord ++ tailWord_1353693).sum := by decide
  have hdescent : baseEnd_1353693 < baseStart_1353693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353738 : List Nat := [3, 1, 2, 2, 5, 1, 2, 6]
def baseStart_1353738 : Nat := 118140960795 + 1353738 * 2 ^ 59
def prefixEnd_1353738 : Nat := 4983230072969 + 3 ^ 40 * 1353738 * 2
def baseEnd_1353738 : Nat := 51490242537505905744391

theorem tailTrace_1353738 : CollatzResearch.WordTrace tailWord_1353738 prefixEnd_1353738 51490242537505905744391 := by
  unfold tailWord_1353738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12343720292411475222183467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32916587446430600592489245 12343720292411475222183467)
  ·
    refine ⟨18515580438617212833275201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12343720292411475222183467 18515580438617212833275201)
    ·
      refine ⟨13886685328962909624956401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18515580438617212833275201 13886685328962909624956401)
      ·
        refine ⟨10415013996722182218717301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13886685328962909624956401 10415013996722182218717301)
        ·
          refine ⟨976407562192704583004747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10415013996722182218717301 976407562192704583004747)
          ·
            refine ⟨1464611343289056874507121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976407562192704583004747 1464611343289056874507121)
            ·
              refine ⟨1098458507466792655880341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464611343289056874507121 1098458507466792655880341)
              ·
                refine ⟨51490242537505905744391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1098458507466792655880341 51490242537505905744391)
                ·
                  rfl

theorem cell22_1353738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_1353738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353738 prefixEnd_1353738 := by exact prefixLift 1353738
  have htrace : WordTrace (prefixWord ++ tailWord_1353738) baseStart_1353738 baseEnd_1353738 := by
    simpa [prefixWord, tailWord_1353738, baseEnd_1353738] using wordTrace_append hprefix tailTrace_1353738
  have hstable : (prefixWord ++ tailWord_1353738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353738).length < 2 ^ (prefixWord ++ tailWord_1353738).sum := by decide
  have hdescent : baseEnd_1353738 < baseStart_1353738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353747 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_1353747 : Nat := 118140960795 + 1353747 * 2 ^ 59
def prefixEnd_1353747 : Nat := 4983230072969 + 3 ^ 40 * 1353747 * 2
def baseEnd_1353747 : Nat := 463415263721480128224491

theorem tailTrace_1353747 : CollatzResearch.WordTrace tailWord_1353747 prefixEnd_1353747 463415263721480128224491 := by
  unfold tailWord_1353747
  simp only [CollatzResearch.WordTrace]
  refine ⟨49375209426613295425811495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32916806284408863617207663 49375209426613295425811495)
  ·
    refine ⟨74062814139919943138717243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49375209426613295425811495 74062814139919943138717243)
    ·
      refine ⟨111094221209879914708075865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74062814139919943138717243 111094221209879914708075865)
      ·
        refine ⟨83320665907409936031056899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111094221209879914708075865 83320665907409936031056899)
        ·
          refine ⟨124980998861114904046585349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83320665907409936031056899 124980998861114904046585349)
          ·
            refine ⟨23433937286459044508734753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124980998861114904046585349 23433937286459044508734753)
            ·
              refine ⟨17575452964844283381551065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23433937286459044508734753 17575452964844283381551065)
              ·
                refine ⟨13181589723633212536163299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17575452964844283381551065 13181589723633212536163299)
                ·
                  refine ⟨19772384585449818804244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13181589723633212536163299 19772384585449818804244949)
                  ·
                    refine ⟨463415263721480128224491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19772384585449818804244949 463415263721480128224491)
                    ·
                      rfl

theorem cell22_1353747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_1353747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353747 prefixEnd_1353747 := by exact prefixLift 1353747
  have htrace : WordTrace (prefixWord ++ tailWord_1353747) baseStart_1353747 baseEnd_1353747 := by
    simpa [prefixWord, tailWord_1353747, baseEnd_1353747] using wordTrace_append hprefix tailTrace_1353747
  have hstable : (prefixWord ++ tailWord_1353747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353747).length < 2 ^ (prefixWord ++ tailWord_1353747).sum := by decide
  have hdescent : baseEnd_1353747 < baseStart_1353747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353813 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_1353813 : Nat := 118140960795 + 1353813 * 2 ^ 59
def prefixEnd_1353813 : Nat := 4983230072969 + 3 ^ 40 * 1353813 * 2
def baseEnd_1353813 : Nat := 463437856870277956074289

theorem tailTrace_1353813 : CollatzResearch.WordTrace tailWord_1353813 prefixEnd_1353813 463437856870277956074289 := by
  unfold tailWord_1353813
  simp only [CollatzResearch.WordTrace]
  refine ⟨49377616644374188697714093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32918411096249459131809395 49377616644374188697714093)
  ·
    refine ⟨18516606241640320761642785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49377616644374188697714093 18516606241640320761642785)
    ·
      refine ⟨13887454681230240571232089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18516606241640320761642785 13887454681230240571232089)
      ·
        refine ⟨10415591010922680428424067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13887454681230240571232089 10415591010922680428424067)
        ·
          refine ⟨15623386516384020642636101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10415591010922680428424067 15623386516384020642636101)
          ·
            refine ⟨2929384971822003870494269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15623386516384020642636101 2929384971822003870494269)
            ·
              refine ⟨1098519364433251451435351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2929384971822003870494269 1098519364433251451435351)
              ·
                refine ⟨1647779046649877177153027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098519364433251451435351 1647779046649877177153027)
                ·
                  refine ⟨2471668569974815765729541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647779046649877177153027 2471668569974815765729541)
                  ·
                    refine ⟨463437856870277956074289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471668569974815765729541 463437856870277956074289)
                    ·
                      rfl

theorem cell22_1353813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_1353813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353813 prefixEnd_1353813 := by exact prefixLift 1353813
  have htrace : WordTrace (prefixWord ++ tailWord_1353813) baseStart_1353813 baseEnd_1353813 := by
    simpa [prefixWord, tailWord_1353813, baseEnd_1353813] using wordTrace_append hprefix tailTrace_1353813
  have hstable : (prefixWord ++ tailWord_1353813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353813).length < 2 ^ (prefixWord ++ tailWord_1353813).sum := by decide
  have hdescent : baseEnd_1353813 < baseStart_1353813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353828 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_1353828 : Nat := 118140960795 + 1353828 * 2 ^ 59
def prefixEnd_1353828 : Nat := 4983230072969 + 3 ^ 40 * 1353828 * 2
def baseEnd_1353828 : Nat := 154480997225607638983081

theorem tailTrace_1353828 : CollatzResearch.WordTrace tailWord_1353828 prefixEnd_1353828 154480997225607638983081 := by
  unfold tailWord_1353828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689081869659923129755069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32918775826213230839673425 24689081869659923129755069)
  ·
    refine ⟨9258405701122471173658151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24689081869659923129755069 9258405701122471173658151)
    ·
      refine ⟨13887608551683706760487227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258405701122471173658151 13887608551683706760487227)
      ·
        refine ⟨20831412827525560140730841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887608551683706760487227 20831412827525560140730841)
        ·
          refine ⟨15623559620644170105548131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20831412827525560140730841 15623559620644170105548131)
          ·
            refine ⟨23435339430966255158322197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15623559620644170105548131 23435339430966255158322197)
            ·
              refine ⟨1098531535826543210546353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23435339430966255158322197 1098531535826543210546353)
              ·
                refine ⟨823898651869907407909765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098531535826543210546353 823898651869907407909765)
                ·
                  refine ⟨154480997225607638983081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 823898651869907407909765 154480997225607638983081)
                  ·
                    rfl

theorem cell22_1353828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_1353828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353828 prefixEnd_1353828 := by exact prefixLift 1353828
  have htrace : WordTrace (prefixWord ++ tailWord_1353828) baseStart_1353828 baseEnd_1353828 := by
    simpa [prefixWord, tailWord_1353828, baseEnd_1353828] using wordTrace_append hprefix tailTrace_1353828
  have hstable : (prefixWord ++ tailWord_1353828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353828).length < 2 ^ (prefixWord ++ tailWord_1353828).sum := by decide
  have hdescent : baseEnd_1353828 < baseStart_1353828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353839 : List Nat := [1, 1, 2, 1, 3, 4, 3, 7]
def baseStart_1353839 : Nat := 118140960795 + 1353839 * 2 ^ 59
def prefixEnd_1353839 : Nat := 4983230072969 + 3 ^ 40 * 1353839 * 2
def baseEnd_1353839 : Nat := 51494084133513617213801

theorem tailTrace_1353839 : CollatzResearch.WordTrace tailWord_1353839 prefixEnd_1353839 51494084133513617213801 := by
  unfold tailWord_1353839
  simp only [CollatzResearch.WordTrace]
  refine ⟨49378564942279995138160571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32919043294853330092107047 49378564942279995138160571)
  ·
    refine ⟨74067847413419992707240857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49378564942279995138160571 74067847413419992707240857)
    ·
      refine ⟨55550885560064994530430643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74067847413419992707240857 55550885560064994530430643)
      ·
        refine ⟨83326328340097491795645965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55550885560064994530430643 83326328340097491795645965)
        ·
          refine ⟨31247373127536559423367237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83326328340097491795645965 31247373127536559423367237)
          ·
            refine ⟨5858882461413104891881357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31247373127536559423367237 5858882461413104891881357)
            ·
              refine ⟨2197080923029914334455509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5858882461413104891881357 2197080923029914334455509)
              ·
                refine ⟨51494084133513617213801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2197080923029914334455509 51494084133513617213801)
                ·
                  rfl

theorem cell22_1353839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 7].length) (baseStart_1353839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353839 prefixEnd_1353839 := by exact prefixLift 1353839
  have htrace : WordTrace (prefixWord ++ tailWord_1353839) baseStart_1353839 baseEnd_1353839 := by
    simpa [prefixWord, tailWord_1353839, baseEnd_1353839] using wordTrace_append hprefix tailTrace_1353839
  have hstable : (prefixWord ++ tailWord_1353839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353839).length < 2 ^ (prefixWord ++ tailWord_1353839).sum := by decide
  have hdescent : baseEnd_1353839 < baseStart_1353839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353888 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_1353888 : Nat := 118140960795 + 1353888 * 2 ^ 59
def prefixEnd_1353888 : Nat := 4983230072969 + 3 ^ 40 * 1353888 * 2
def baseEnd_1353888 : Nat := 463463530903002760449059

theorem tailTrace_1353888 : CollatzResearch.WordTrace tailWord_1353888 prefixEnd_1353888 463463530903002760449059 := by
  unfold tailWord_1353888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24690176059551238253347159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32920234746068317671129545 24690176059551238253347159)
  ·
    refine ⟨37035264089326857380020739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24690176059551238253347159 37035264089326857380020739)
    ·
      refine ⟨55552896133990286070031109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37035264089326857380020739 55552896133990286070031109)
      ·
        refine ⟨10416168025123178638130833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55552896133990286070031109 10416168025123178638130833)
        ·
          refine ⟨7812126018842383978598125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10416168025123178638130833 7812126018842383978598125)
          ·
            refine ⟨2929547257065893991974297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7812126018842383978598125 2929547257065893991974297)
            ·
              refine ⟨2197160442799420493980723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929547257065893991974297 2197160442799420493980723)
              ·
                refine ⟨3295740664199130740971085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197160442799420493980723 3295740664199130740971085)
                ·
                  refine ⟨1235902749074674027864157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3295740664199130740971085 1235902749074674027864157)
                  ·
                    refine ⟨463463530903002760449059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235902749074674027864157 463463530903002760449059)
                    ·
                      rfl

theorem cell22_1353888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_1353888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353888 prefixEnd_1353888 := by exact prefixLift 1353888
  have htrace : WordTrace (prefixWord ++ tailWord_1353888) baseStart_1353888 baseEnd_1353888 := by
    simpa [prefixWord, tailWord_1353888, baseEnd_1353888] using wordTrace_append hprefix tailTrace_1353888
  have hstable : (prefixWord ++ tailWord_1353888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353888).length < 2 ^ (prefixWord ++ tailWord_1353888).sum := by decide
  have hdescent : baseEnd_1353888 < baseStart_1353888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353931 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 1, 4]
def baseStart_1353931 : Nat := 118140960795 + 1353931 * 2 ^ 59
def prefixEnd_1353931 : Nat := 4983230072969 + 3 ^ 40 * 1353931 * 2
def baseEnd_1353931 : Nat := 463478250681764981623927

theorem tailTrace_1353931 : CollatzResearch.WordTrace tailWord_1353931 prefixEnd_1353931 463478250681764981623927 := by
  unfold tailWord_1353931
  simp only [CollatzResearch.WordTrace]
  refine ⟨49381920457946694850509647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32921280305297796567006431 49381920457946694850509647)
  ·
    refine ⟨74072880686920042275764471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49381920457946694850509647 74072880686920042275764471)
    ·
      refine ⟨111109321030380063413646707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74072880686920042275764471 111109321030380063413646707)
      ·
        refine ⟨166663981545570095120470061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111109321030380063413646707 166663981545570095120470061)
        ·
          refine ⟨62498993079588785670176273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166663981545570095120470061 62498993079588785670176273)
          ·
            refine ⟨46874244809691589252632205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62498993079588785670176273 46874244809691589252632205)
            ·
              refine ⟨17577841803634345969737077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46874244809691589252632205 17577841803634345969737077)
              ·
                refine ⟨1647922669090719934662851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17577841803634345969737077 1647922669090719934662851)
                ·
                  refine ⟨2471884003636079901994277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647922669090719934662851 2471884003636079901994277)
                  ·
                    refine ⟨463478250681764981623927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471884003636079901994277 463478250681764981623927)
                    ·
                      rfl

theorem cell22_1353931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_1353931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353931 prefixEnd_1353931 := by exact prefixLift 1353931
  have htrace : WordTrace (prefixWord ++ tailWord_1353931) baseStart_1353931 baseEnd_1353931 := by
    simpa [prefixWord, tailWord_1353931, baseEnd_1353931] using wordTrace_append hprefix tailTrace_1353931
  have hstable : (prefixWord ++ tailWord_1353931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353931).length < 2 ^ (prefixWord ++ tailWord_1353931).sum := by decide
  have hdescent : baseEnd_1353931 < baseStart_1353931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353946 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1353946 : Nat := 118140960795 + 1353946 * 2 ^ 59
def prefixEnd_1353946 : Nat := 4983230072969 + 3 ^ 40 * 1353946 * 2
def baseEnd_1353946 : Nat := 154494461829436647499627

theorem tailTrace_1353946 : CollatzResearch.WordTrace tailWord_1353946 prefixEnd_1353946 154494461829436647499627 := by
  unfold tailWord_1353946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345616888223088103076423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32921645035261568274870461 12345616888223088103076423)
  ·
    refine ⟨18518425332334632154614635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12345616888223088103076423 18518425332334632154614635)
    ·
      refine ⟨27777637998501948231921953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18518425332334632154614635 27777637998501948231921953)
      ·
        refine ⟨20833228498876461173941465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27777637998501948231921953 20833228498876461173941465)
        ·
          refine ⟨15624921374157345880456099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20833228498876461173941465 15624921374157345880456099)
          ·
            refine ⟨23437382061236018820684149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15624921374157345880456099 23437382061236018820684149)
            ·
              refine ⟨2197254568240876764439139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23437382061236018820684149 2197254568240876764439139)
              ·
                refine ⟨3295881852361315146658709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197254568240876764439139 3295881852361315146658709)
                ·
                  refine ⟨154494461829436647499627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3295881852361315146658709 154494461829436647499627)
                  ·
                    rfl

theorem cell22_1353946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1353946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353946 prefixEnd_1353946 := by exact prefixLift 1353946
  have htrace : WordTrace (prefixWord ++ tailWord_1353946) baseStart_1353946 baseEnd_1353946 := by
    simpa [prefixWord, tailWord_1353946, baseEnd_1353946] using wordTrace_append hprefix tailTrace_1353946
  have hstable : (prefixWord ++ tailWord_1353946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353946).length < 2 ^ (prefixWord ++ tailWord_1353946).sum := by decide
  have hdescent : baseEnd_1353946 < baseStart_1353946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353991 : List Nat := [1, 1, 4, 5, 11]
def baseStart_1353991 : Nat := 118140960795 + 1353991 * 2 ^ 59
def prefixEnd_1353991 : Nat := 4983230072969 + 3 ^ 40 * 1353991 * 2
def baseEnd_1353991 : Nat := 1907402427604711214501

theorem tailTrace_1353991 : CollatzResearch.WordTrace tailWord_1353991 prefixEnd_1353991 1907402427604711214501 := by
  unfold tailWord_1353991
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384108837729325097693827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32922739225152883398462551 49384108837729325097693827)
  ·
    refine ⟨74076163256593987646540741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49384108837729325097693827 74076163256593987646540741)
    ·
      refine ⟨13889280610611372683726389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74076163256593987646540741 13889280610611372683726389)
      ·
        refine ⟨1302120057244816189099349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13889280610611372683726389 1302120057244816189099349)
        ·
          refine ⟨1907402427604711214501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1302120057244816189099349 1907402427604711214501)
          ·
            rfl

theorem cell22_1353991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 11].length) (baseStart_1353991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1353991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1353991 prefixEnd_1353991 := by exact prefixLift 1353991
  have htrace : WordTrace (prefixWord ++ tailWord_1353991) baseStart_1353991 baseEnd_1353991 := by
    simpa [prefixWord, tailWord_1353991, baseEnd_1353991] using wordTrace_append hprefix tailTrace_1353991
  have hstable : (prefixWord ++ tailWord_1353991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353991).length < 2 ^ (prefixWord ++ tailWord_1353991).sum := by decide
  have hdescent : baseEnd_1353991 < baseStart_1353991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354040 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1354040 : Nat := 118140960795 + 1354040 * 2 ^ 59
def prefixEnd_1354040 : Nat := 4983230072969 + 3 ^ 40 * 1354040 * 2
def baseEnd_1354040 : Nat := 463515563609325030648593

theorem tailTrace_1354040 : CollatzResearch.WordTrace tailWord_1354040 prefixEnd_1354040 463515563609325030648593 := by
  unfold tailWord_1354040
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692948007275903233113787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32923930676367870977485049 24692948007275903233113787)
  ·
    refine ⟨37039422010913854849670681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24692948007275903233113787 37039422010913854849670681)
    ·
      refine ⟨27779566508185391137253011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37039422010913854849670681 27779566508185391137253011)
      ·
        refine ⟨41669349762278086705879517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27779566508185391137253011 41669349762278086705879517)
        ·
          refine ⟨15626006160854282514704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41669349762278086705879517 15626006160854282514704819)
          ·
            refine ⟨23439009241281423772057229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15626006160854282514704819 23439009241281423772057229)
            ·
              refine ⟨8789628465480533914521461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23439009241281423772057229 8789628465480533914521461)
              ·
                refine ⟨824027668638800054486387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8789628465480533914521461 824027668638800054486387)
                ·
                  refine ⟨1236041502958200081729581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824027668638800054486387 1236041502958200081729581)
                  ·
                    refine ⟨463515563609325030648593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236041502958200081729581 463515563609325030648593)
                    ·
                      rfl

theorem cell22_1354040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1354040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354040 prefixEnd_1354040 := by exact prefixLift 1354040
  have htrace : WordTrace (prefixWord ++ tailWord_1354040) baseStart_1354040 baseEnd_1354040 := by
    simpa [prefixWord, tailWord_1354040, baseEnd_1354040] using wordTrace_append hprefix tailTrace_1354040
  have hstable : (prefixWord ++ tailWord_1354040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354040).length < 2 ^ (prefixWord ++ tailWord_1354040).sum := by decide
  have hdescent : baseEnd_1354040 < baseStart_1354040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354051 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_1354051 : Nat := 118140960795 + 1354051 * 2 ^ 59
def prefixEnd_1354051 : Nat := 4983230072969 + 3 ^ 40 * 1354051 * 2
def baseEnd_1354051 : Nat := 463519329134124668623559

theorem tailTrace_1354051 : CollatzResearch.WordTrace tailWord_1354051 prefixEnd_1354051 463519329134124668623559 := by
  unfold tailWord_1354051
  simp only [CollatzResearch.WordTrace]
  refine ⟨49386297217511955344878007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32924198145007970229918671 49386297217511955344878007)
  ·
    refine ⟨74079445826267933017317011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49386297217511955344878007 74079445826267933017317011)
    ·
      refine ⟨111119168739401899525975517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74079445826267933017317011 111119168739401899525975517)
      ·
        refine ⟨41669688277275712322240819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111119168739401899525975517 41669688277275712322240819)
        ·
          refine ⟨62504532415913568483361229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41669688277275712322240819 62504532415913568483361229)
          ·
            refine ⟨23439199655967588181260461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62504532415913568483361229 23439199655967588181260461)
            ·
              refine ⟨8789699870987845567972673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23439199655967588181260461 8789699870987845567972673)
              ·
                refine ⟨6592274903240884175979505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789699870987845567972673 6592274903240884175979505)
                ·
                  refine ⟨4944206177430663131984629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592274903240884175979505 4944206177430663131984629)
                  ·
                    refine ⟨463519329134124668623559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4944206177430663131984629 463519329134124668623559)
                    ·
                      rfl

theorem cell22_1354051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_1354051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354051 prefixEnd_1354051 := by exact prefixLift 1354051
  have htrace : WordTrace (prefixWord ++ tailWord_1354051) baseStart_1354051 baseEnd_1354051 := by
    simpa [prefixWord, tailWord_1354051, baseEnd_1354051] using wordTrace_append hprefix tailTrace_1354051
  have hstable : (prefixWord ++ tailWord_1354051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354051).length < 2 ^ (prefixWord ++ tailWord_1354051).sum := by decide
  have hdescent : baseEnd_1354051 < baseStart_1354051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354068 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1354068 : Nat := 118140960795 + 1354068 * 2 ^ 59
def prefixEnd_1354068 : Nat := 4983230072969 + 3 ^ 40 * 1354068 * 2
def baseEnd_1354068 : Nat := 463525148581542290948507

theorem tailTrace_1354068 : CollatzResearch.WordTrace tailWord_1354068 prefixEnd_1354068 463525148581542290948507 := by
  unfold tailWord_1354068
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693458629225183624123429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32924611505633578165497905 24693458629225183624123429)
  ·
    refine ⟨4630023492979721929523143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24693458629225183624123429 4630023492979721929523143)
    ·
      refine ⟨6945035239469582894284715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630023492979721929523143 6945035239469582894284715)
      ·
        refine ⟨10417552859204374341427073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6945035239469582894284715 10417552859204374341427073)
        ·
          refine ⟨7813164644403280756070305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10417552859204374341427073 7813164644403280756070305)
          ·
            refine ⟨5859873483302460567052729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813164644403280756070305 5859873483302460567052729)
            ·
              refine ⟨4394905112476845425289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859873483302460567052729 4394905112476845425289547)
              ·
                refine ⟨6592357668715268137934321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394905112476845425289547 6592357668715268137934321)
                ·
                  refine ⟨4944268251536451103450741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592357668715268137934321 4944268251536451103450741)
                  ·
                    refine ⟨463525148581542290948507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4944268251536451103450741 463525148581542290948507)
                    ·
                      rfl

theorem cell22_1354068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1354068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354068 prefixEnd_1354068 := by exact prefixLift 1354068
  have htrace : WordTrace (prefixWord ++ tailWord_1354068) baseStart_1354068 baseEnd_1354068 := by
    simpa [prefixWord, tailWord_1354068, baseEnd_1354068] using wordTrace_append hprefix tailTrace_1354068
  have hstable : (prefixWord ++ tailWord_1354068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354068).length < 2 ^ (prefixWord ++ tailWord_1354068).sum := by decide
  have hdescent : baseEnd_1354068 < baseStart_1354068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354115 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 6]
def baseStart_1354115 : Nat := 118140960795 + 1354115 * 2 ^ 59
def prefixEnd_1354115 : Nat := 4983230072969 + 3 ^ 40 * 1354115 * 2
def baseEnd_1354115 : Nat := 154513745880683278341121

theorem tailTrace_1354115 : CollatzResearch.WordTrace tailWord_1354115 prefixEnd_1354115 154513745880683278341121 := by
  unfold tailWord_1354115
  simp only [CollatzResearch.WordTrace]
  refine ⟨49388631489280094275207799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32925754326186729516805199 49388631489280094275207799)
  ·
    refine ⟨74082947233920141412811699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49388631489280094275207799 74082947233920141412811699)
    ·
      refine ⟨111124420850880212119217549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74082947233920141412811699 111124420850880212119217549)
      ·
        refine ⟨41671657819080079544706581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111124420850880212119217549 41671657819080079544706581)
        ·
          refine ⟨1953358960269378728658121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41671657819080079544706581 1953358960269378728658121)
          ·
            refine ⟨1465019220202034046493591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953358960269378728658121 1465019220202034046493591)
            ·
              refine ⟨2197528830303051069740387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465019220202034046493591 2197528830303051069740387)
              ·
                refine ⟨3296293245454576604610581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197528830303051069740387 3296293245454576604610581)
                ·
                  refine ⟨154513745880683278341121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3296293245454576604610581 154513745880683278341121)
                  ·
                    rfl

theorem cell22_1354115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].length) (baseStart_1354115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354115 prefixEnd_1354115 := by exact prefixLift 1354115
  have htrace : WordTrace (prefixWord ++ tailWord_1354115) baseStart_1354115 baseEnd_1354115 := by
    simpa [prefixWord, tailWord_1354115, baseEnd_1354115] using wordTrace_append hprefix tailTrace_1354115
  have hstable : (prefixWord ++ tailWord_1354115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354115).length < 2 ^ (prefixWord ++ tailWord_1354115).sum := by decide
  have hdescent : baseEnd_1354115 < baseStart_1354115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354173 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1354173 : Nat := 118140960795 + 1354173 * 2 ^ 59
def prefixEnd_1354173 : Nat := 4983230072969 + 3 ^ 40 * 1354173 * 2
def baseEnd_1354173 : Nat := 463561092227357017073185

theorem tailTrace_1354173 : CollatzResearch.WordTrace tailWord_1354173 prefixEnd_1354173 463561092227357017073185 := by
  unfold tailWord_1354173
  simp only [CollatzResearch.WordTrace]
  refine ⟨49390746923069970180819173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32927164615379980120546115 49390746923069970180819173)
  ·
    refine ⟨9260765048075619408903595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49390746923069970180819173 9260765048075619408903595)
    ·
      refine ⟨13891147572113429113355393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9260765048075619408903595 13891147572113429113355393)
      ·
        refine ⟨10418360679085071835016545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13891147572113429113355393 10418360679085071835016545)
        ·
          refine ⟨7813770509313803876262409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10418360679085071835016545 7813770509313803876262409)
          ·
            refine ⟨5860327881985352907196807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813770509313803876262409 5860327881985352907196807)
            ·
              refine ⟨8790491822978029360795211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860327881985352907196807 8790491822978029360795211)
              ·
                refine ⟨13185737734467044041192817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790491822978029360795211 13185737734467044041192817)
                ·
                  refine ⟨9889303300850283030894613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13185737734467044041192817 9889303300850283030894613)
                  ·
                    refine ⟨463561092227357017073185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9889303300850283030894613 463561092227357017073185)
                    ·
                      rfl

theorem cell22_1354173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1354173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354173 prefixEnd_1354173 := by exact prefixLift 1354173
  have htrace : WordTrace (prefixWord ++ tailWord_1354173) baseStart_1354173 baseEnd_1354173 := by
    simpa [prefixWord, tailWord_1354173, baseEnd_1354173] using wordTrace_append hprefix tailTrace_1354173
  have hstable : (prefixWord ++ tailWord_1354173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354173).length < 2 ^ (prefixWord ++ tailWord_1354173).sum := by decide
  have hdescent : baseEnd_1354173 < baseStart_1354173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354222 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1354222 : Nat := 118140960795 + 1354222 * 2 ^ 59
def prefixEnd_1354222 : Nat := 4983230072969 + 3 ^ 40 * 1354222 * 2
def baseEnd_1354222 : Nat := 154525955309579074199345

theorem tailTrace_1354222 : CollatzResearch.WordTrace tailWord_1354222 prefixEnd_1354222 154525955309579074199345 := by
  unfold tailWord_1354222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174066762486556443669115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32928356066594967699568613 6174066762486556443669115)
  ·
    refine ⟨9261100143729834665503673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174066762486556443669115 9261100143729834665503673)
    ·
      refine ⟨6945825107797375999127755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9261100143729834665503673 6945825107797375999127755)
      ·
        refine ⟨10418737661696063998691633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6945825107797375999127755 10418737661696063998691633)
        ·
          refine ⟨7814053246272047999018725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10418737661696063998691633 7814053246272047999018725)
          ·
            refine ⟨1465134983676008999816011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7814053246272047999018725 1465134983676008999816011)
            ·
              refine ⟨2197702475514013499724017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465134983676008999816011 2197702475514013499724017)
              ·
                refine ⟨1648276856635510124793013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197702475514013499724017 1648276856635510124793013)
                ·
                  refine ⟨154525955309579074199345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1648276856635510124793013 154525955309579074199345)
                  ·
                    rfl

theorem cell22_1354222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1354222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354222 prefixEnd_1354222 := by exact prefixLift 1354222
  have htrace : WordTrace (prefixWord ++ tailWord_1354222) baseStart_1354222 baseEnd_1354222 := by
    simpa [prefixWord, tailWord_1354222, baseEnd_1354222] using wordTrace_append hprefix tailTrace_1354222
  have hstable : (prefixWord ++ tailWord_1354222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354222).length < 2 ^ (prefixWord ++ tailWord_1354222).sum := by decide
  have hdescent : baseEnd_1354222 < baseStart_1354222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354233 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 6]
def baseStart_1354233 : Nat := 118140960795 + 1354233 * 2 ^ 59
def prefixEnd_1354233 : Nat := 4983230072969 + 3 ^ 40 * 1354233 * 2
def baseEnd_1354233 : Nat := 154527210484512286857667

theorem tailTrace_1354233 : CollatzResearch.WordTrace tailWord_1354233 prefixEnd_1354233 154527210484512286857667 := by
  unfold tailWord_1354233
  simp only [CollatzResearch.WordTrace]
  refine ⟨49392935302852600428003353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32928623535235066952002235 49392935302852600428003353)
  ·
    refine ⟨37044701477139450321002515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49392935302852600428003353 37044701477139450321002515)
    ·
      refine ⟨55567052215709175481503773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37044701477139450321002515 55567052215709175481503773)
      ·
        refine ⟨20837644580890940805563915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55567052215709175481503773 20837644580890940805563915)
        ·
          refine ⟨31256466871336411208345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20837644580890940805563915 31256466871336411208345873)
          ·
            refine ⟨23442350153502308406259405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31256466871336411208345873 23442350153502308406259405)
            ·
              refine ⟨8790881307563365652347277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23442350153502308406259405 8790881307563365652347277)
              ·
                refine ⟨3296580490336262119630229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8790881307563365652347277 3296580490336262119630229)
                ·
                  refine ⟨154527210484512286857667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3296580490336262119630229 154527210484512286857667)
                  ·
                    rfl

theorem cell22_1354233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_1354233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354233 prefixEnd_1354233 := by exact prefixLift 1354233
  have htrace : WordTrace (prefixWord ++ tailWord_1354233) baseStart_1354233 baseEnd_1354233 := by
    simpa [prefixWord, tailWord_1354233, baseEnd_1354233] using wordTrace_append hprefix tailTrace_1354233
  have hstable : (prefixWord ++ tailWord_1354233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354233).length < 2 ^ (prefixWord ++ tailWord_1354233).sum := by decide
  have hdescent : baseEnd_1354233 < baseStart_1354233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354252 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1354252 : Nat := 118140960795 + 1354252 * 2 ^ 59
def prefixEnd_1354252 : Nat := 4983230072969 + 3 ^ 40 * 1354252 * 2
def baseEnd_1354252 : Nat := 463588135541827144347943

theorem tailTrace_1354252 : CollatzResearch.WordTrace tailWord_1354252 prefixEnd_1354252 463588135541827144347943 := by
  unfold tailWord_1354252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696814144891883336472505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32929085526522511115296673 24696814144891883336472505)
  ·
    refine ⟨18522610608668912502354379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24696814144891883336472505 18522610608668912502354379)
    ·
      refine ⟨27783915913003368753531569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522610608668912502354379 27783915913003368753531569)
      ·
        refine ⟨20837936934752526565148677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27783915913003368753531569 20837936934752526565148677)
        ·
          refine ⟨3907113175266098730965377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20837936934752526565148677 3907113175266098730965377)
          ·
            refine ⟨2930334881449574048224033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907113175266098730965377 2930334881449574048224033)
            ·
              refine ⟨2197751161087180536168025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2930334881449574048224033 2197751161087180536168025)
              ·
                refine ⟨1648313370815385402126019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197751161087180536168025 1648313370815385402126019)
                ·
                  refine ⟨2472470056223078103189029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648313370815385402126019 2472470056223078103189029)
                  ·
                    refine ⟨463588135541827144347943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472470056223078103189029 463588135541827144347943)
                    ·
                      rfl

theorem cell22_1354252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1354252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354252 prefixEnd_1354252 := by exact prefixLift 1354252
  have htrace : WordTrace (prefixWord ++ tailWord_1354252) baseStart_1354252 baseEnd_1354252 := by
    simpa [prefixWord, tailWord_1354252, baseEnd_1354252] using wordTrace_append hprefix tailTrace_1354252
  have hstable : (prefixWord ++ tailWord_1354252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354252).length < 2 ^ (prefixWord ++ tailWord_1354252).sum := by decide
  have hdescent : baseEnd_1354252 < baseStart_1354252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354282 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1354282 : Nat := 118140960795 + 1354282 * 2 ^ 59
def prefixEnd_1354282 : Nat := 4983230072969 + 3 ^ 40 * 1354282 * 2
def baseEnd_1354282 : Nat := 463598405154917066097851

theorem tailTrace_1354282 : CollatzResearch.WordTrace tailWord_1354282 prefixEnd_1354282 463598405154917066097851 := by
  unfold tailWord_1354282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12348680619918770449134275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32929814986450054531024733 12348680619918770449134275)
  ·
    refine ⟨18523020929878155673701413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12348680619918770449134275 18523020929878155673701413)
    ·
      refine ⟨3473066424352154188819015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18523020929878155673701413 3473066424352154188819015)
      ·
        refine ⟨5209599636528231283228523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473066424352154188819015 5209599636528231283228523)
        ·
          refine ⟨7814399454792346924842785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209599636528231283228523 7814399454792346924842785)
          ·
            refine ⟨5860799591094260193632089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7814399454792346924842785 5860799591094260193632089)
            ·
              refine ⟨4395599693320695145224067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5860799591094260193632089 4395599693320695145224067)
              ·
                refine ⟨6593399539981042717836101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395599693320695145224067 6593399539981042717836101)
                ·
                  refine ⟨1236262413746445509594269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6593399539981042717836101 1236262413746445509594269)
                  ·
                    refine ⟨463598405154917066097851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236262413746445509594269 463598405154917066097851)
                    ·
                      rfl

theorem cell22_1354282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1354282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354282 prefixEnd_1354282 := by exact prefixLift 1354282
  have htrace : WordTrace (prefixWord ++ tailWord_1354282) baseStart_1354282 baseEnd_1354282 := by
    simpa [prefixWord, tailWord_1354282, baseEnd_1354282] using wordTrace_append hprefix tailTrace_1354282
  have hstable : (prefixWord ++ tailWord_1354282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354282).length < 2 ^ (prefixWord ++ tailWord_1354282).sum := by decide
  have hdescent : baseEnd_1354282 < baseStart_1354282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354415 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1354415 : Nat := 118140960795 + 1354415 * 2 ^ 59
def prefixEnd_1354415 : Nat := 4983230072969 + 3 ^ 40 * 1354415 * 2
def baseEnd_1354415 : Nat := 463643933772949052522443

theorem tailTrace_1354415 : CollatzResearch.WordTrace tailWord_1354415 prefixEnd_1354415 463643933772949052522443 := by
  unfold tailWord_1354415
  simp only [CollatzResearch.WordTrace]
  refine ⟨49399573388193245511128699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32933048925462163674085799 49399573388193245511128699)
  ·
    refine ⟨74099360082289868266693049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49399573388193245511128699 74099360082289868266693049)
    ·
      refine ⟨55574520061717401200019787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74099360082289868266693049 55574520061717401200019787)
      ·
        refine ⟨83361780092576101800029681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55574520061717401200019787 83361780092576101800029681)
        ·
          refine ⟨62521335069432076350022261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83361780092576101800029681 62521335069432076350022261)
          ·
            refine ⟨5861375162759257157814587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62521335069432076350022261 5861375162759257157814587)
            ·
              refine ⟨8792062744138885736721881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861375162759257157814587 8792062744138885736721881)
              ·
                refine ⟨6594047058104164302541411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792062744138885736721881 6594047058104164302541411)
                ·
                  refine ⟨9891070587156246453812117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594047058104164302541411 9891070587156246453812117)
                  ·
                    refine ⟨463643933772949052522443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9891070587156246453812117 463643933772949052522443)
                    ·
                      rfl

theorem cell22_1354415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1354415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354415 prefixEnd_1354415 := by exact prefixLift 1354415
  have htrace : WordTrace (prefixWord ++ tailWord_1354415) baseStart_1354415 baseEnd_1354415 := by
    simpa [prefixWord, tailWord_1354415, baseEnd_1354415] using wordTrace_append hprefix tailTrace_1354415
  have hstable : (prefixWord ++ tailWord_1354415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354415).length < 2 ^ (prefixWord ++ tailWord_1354415).sum := by decide
  have hdescent : baseEnd_1354415 < baseStart_1354415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354436 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1354436 : Nat := 118140960795 + 1354436 * 2 ^ 59
def prefixEnd_1354436 : Nat := 4983230072969 + 3 ^ 40 * 1354436 * 2
def baseEnd_1354436 : Nat := 154550374167370665915793

theorem tailTrace_1354436 : CollatzResearch.WordTrace tailWord_1354436 prefixEnd_1354436 154550374167370665915793 := by
  unfold tailWord_1354436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700169660558583048821581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32933559547411444065095441 24700169660558583048821581)
  ·
    refine ⟨9262563622709468643308093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24700169660558583048821581 9262563622709468643308093)
    ·
      refine ⟨3473461358516050741240535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9262563622709468643308093 3473461358516050741240535)
      ·
        refine ⟨5210192037774076111860803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473461358516050741240535 5210192037774076111860803)
        ·
          refine ⟨7815288056661114167791205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210192037774076111860803 7815288056661114167791205)
          ·
            refine ⟨1465366510623958906460851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7815288056661114167791205 1465366510623958906460851)
            ·
              refine ⟨2198049765935938359691277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465366510623958906460851 2198049765935938359691277)
              ·
                refine ⟨824268662225976884884229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198049765935938359691277 824268662225976884884229)
                ·
                  refine ⟨154550374167370665915793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824268662225976884884229 154550374167370665915793)
                  ·
                    rfl

theorem cell22_1354436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1354436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354436 prefixEnd_1354436 := by exact prefixLift 1354436
  have htrace : WordTrace (prefixWord ++ tailWord_1354436) baseStart_1354436 baseEnd_1354436 := by
    simpa [prefixWord, tailWord_1354436, baseEnd_1354436] using wordTrace_append hprefix tailTrace_1354436
  have hstable : (prefixWord ++ tailWord_1354436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354436).length < 2 ^ (prefixWord ++ tailWord_1354436).sum := by decide
  have hdescent : baseEnd_1354436 < baseStart_1354436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354453 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1354453 : Nat := 118140960795 + 1354453 * 2 ^ 59
def prefixEnd_1354453 : Nat := 4983230072969 + 3 ^ 40 * 1354453 * 2
def baseEnd_1354453 : Nat := 154552313983176540024109

theorem tailTrace_1354453 : CollatzResearch.WordTrace tailWord_1354453 prefixEnd_1354453 154552313983176540024109 := by
  unfold tailWord_1354453
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400959362055578001012013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32933972908037052000674675 49400959362055578001012013)
  ·
    refine ⟨18525359760770841750379505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49400959362055578001012013 18525359760770841750379505)
    ·
      refine ⟨13894019820578131312784629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18525359760770841750379505 13894019820578131312784629)
      ·
        refine ⟨1302564358179199810573559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13894019820578131312784629 1302564358179199810573559)
        ·
          refine ⟨1953846537268799715860339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302564358179199810573559 1953846537268799715860339)
          ·
            refine ⟨2930769805903199573790509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953846537268799715860339 2930769805903199573790509)
            ·
              refine ⟨1099038677213699840171441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2930769805903199573790509 1099038677213699840171441)
              ·
                refine ⟨824279007910274880128581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099038677213699840171441 824279007910274880128581)
                ·
                  refine ⟨154552313983176540024109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824279007910274880128581 154552313983176540024109)
                  ·
                    rfl

theorem cell22_1354453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1354453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354453 prefixEnd_1354453 := by exact prefixLift 1354453
  have htrace : WordTrace (prefixWord ++ tailWord_1354453) baseStart_1354453 baseEnd_1354453 := by
    simpa [prefixWord, tailWord_1354453, baseEnd_1354453] using wordTrace_append hprefix tailTrace_1354453
  have hstable : (prefixWord ++ tailWord_1354453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354453).length < 2 ^ (prefixWord ++ tailWord_1354453).sum := by decide
  have hdescent : baseEnd_1354453 < baseStart_1354453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354522 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1354522 : Nat := 118140960795 + 1354522 * 2 ^ 59
def prefixEnd_1354522 : Nat := 4983230072969 + 3 ^ 40 * 1354522 * 2
def baseEnd_1354522 : Nat := 463680562059636440097115

theorem tailTrace_1354522 : CollatzResearch.WordTrace tailWord_1354522 prefixEnd_1354522 463680562059636440097115 := by
  unfold tailWord_1354522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350868999701400696318455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32935650665870401856849213 12350868999701400696318455)
  ·
    refine ⟨18526303499552101044477683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12350868999701400696318455 18526303499552101044477683)
    ·
      refine ⟨27789455249328151566716525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18526303499552101044477683 27789455249328151566716525)
      ·
        refine ⟨10421045718498056837518697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27789455249328151566716525 10421045718498056837518697)
        ·
          refine ⟨7815784288873542628139023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10421045718498056837518697 7815784288873542628139023)
          ·
            refine ⟨11723676433310313942208535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815784288873542628139023 11723676433310313942208535)
            ·
              refine ⟨17585514649965470913312803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723676433310313942208535 17585514649965470913312803)
              ·
                refine ⟨26378271974948206369969205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17585514649965470913312803 26378271974948206369969205)
                ·
                  refine ⟨2472962997651394347184613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26378271974948206369969205 2472962997651394347184613)
                  ·
                    refine ⟨463680562059636440097115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472962997651394347184613 463680562059636440097115)
                    ·
                      rfl

theorem cell22_1354522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1354522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354522 prefixEnd_1354522 := by exact prefixLift 1354522
  have htrace : WordTrace (prefixWord ++ tailWord_1354522) baseStart_1354522 baseEnd_1354522 := by
    simpa [prefixWord, tailWord_1354522, baseEnd_1354522] using wordTrace_append hprefix tailTrace_1354522
  have hstable : (prefixWord ++ tailWord_1354522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354522).length < 2 ^ (prefixWord ++ tailWord_1354522).sum := by decide
  have hdescent : baseEnd_1354522 < baseStart_1354522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354552 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1354552 : Nat := 118140960795 + 1354552 * 2 ^ 59
def prefixEnd_1354552 : Nat := 4983230072969 + 3 ^ 40 * 1354552 * 2
def baseEnd_1354552 : Nat := 463690831672726361847023

theorem tailTrace_1354552 : CollatzResearch.WordTrace tailWord_1354552 prefixEnd_1354552 463690831672726361847023 := by
  unfold tailWord_1354552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24702285094348458954432955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32936380125797945272577273 24702285094348458954432955)
  ·
    refine ⟨37053427641522688431649433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24702285094348458954432955 37053427641522688431649433)
    ·
      refine ⟨27790070731142016323737075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37053427641522688431649433 27790070731142016323737075)
      ·
        refine ⟨41685106096713024485605613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27790070731142016323737075 41685106096713024485605613)
        ·
          refine ⟨15631914786267384182102105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41685106096713024485605613 15631914786267384182102105)
          ·
            refine ⟨11723936089700538136576579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15631914786267384182102105 11723936089700538136576579)
            ·
              refine ⟨17585904134550807204864869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723936089700538136576579 17585904134550807204864869)
              ·
                refine ⟨3297357025228276350912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17585904134550807204864869 3297357025228276350912163)
                ·
                  refine ⟨4946035537842414526368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297357025228276350912163 4946035537842414526368245)
                  ·
                    refine ⟨463690831672726361847023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4946035537842414526368245 463690831672726361847023)
                    ·
                      rfl

theorem cell22_1354552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1354552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354552 prefixEnd_1354552 := by exact prefixLift 1354552
  have htrace : WordTrace (prefixWord ++ tailWord_1354552) baseStart_1354552 baseEnd_1354552 := by
    simpa [prefixWord, tailWord_1354552, baseEnd_1354552] using wordTrace_append hprefix tailTrace_1354552
  have hstable : (prefixWord ++ tailWord_1354552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354552).length < 2 ^ (prefixWord ++ tailWord_1354552).sum := by decide
  have hdescent : baseEnd_1354552 < baseStart_1354552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354567 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1354567 : Nat := 118140960795 + 1354567 * 2 ^ 59
def prefixEnd_1354567 : Nat := 4983230072969 + 3 ^ 40 * 1354567 * 2
def baseEnd_1354567 : Nat := 463695966479271322721977

theorem tailTrace_1354567 : CollatzResearch.WordTrace tailWord_1354567 prefixEnd_1354567 463695966479271322721977 := by
  unfold tailWord_1354567
  simp only [CollatzResearch.WordTrace]
  refine ⟨49405117283642575470661955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32936744855761716980441303 49405117283642575470661955)
  ·
    refine ⟨74107675925463863205992933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49405117283642575470661955 74107675925463863205992933)
    ·
      refine ⟨13895189236024474351123675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74107675925463863205992933 13895189236024474351123675)
      ·
        refine ⟨20842783854036711526685513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13895189236024474351123675 20842783854036711526685513)
        ·
          refine ⟨15632087890527533645014135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20842783854036711526685513 15632087890527533645014135)
          ·
            refine ⟨23448131835791300467521203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632087890527533645014135 23448131835791300467521203)
            ·
              refine ⟨35172197753686950701281805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448131835791300467521203 35172197753686950701281805)
              ·
                refine ⟨13189574157632606512980677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35172197753686950701281805 13189574157632606512980677)
                ·
                  refine ⟨2473045154556113721183877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13189574157632606512980677 2473045154556113721183877)
                  ·
                    refine ⟨463695966479271322721977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473045154556113721183877 463695966479271322721977)
                    ·
                      rfl

theorem cell22_1354567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1354567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354567 prefixEnd_1354567 := by exact prefixLift 1354567
  have htrace : WordTrace (prefixWord ++ tailWord_1354567) baseStart_1354567 baseEnd_1354567 := by
    simpa [prefixWord, tailWord_1354567, baseEnd_1354567] using wordTrace_append hprefix tailTrace_1354567
  have hstable : (prefixWord ++ tailWord_1354567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354567).length < 2 ^ (prefixWord ++ tailWord_1354567).sum := by decide
  have hdescent : baseEnd_1354567 < baseStart_1354567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354569 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_1354569 : Nat := 118140960795 + 1354569 * 2 ^ 59
def prefixEnd_1354569 : Nat := 4983230072969 + 3 ^ 40 * 1354569 * 2
def baseEnd_1354569 : Nat := 463696651120143984171971

theorem tailTrace_1354569 : CollatzResearch.WordTrace tailWord_1354569 prefixEnd_1354569 463696651120143984171971 := by
  unfold tailWord_1354569
  simp only [CollatzResearch.WordTrace]
  refine ⟨49405190229635329812234761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32936793486423553208156507 49405190229635329812234761)
  ·
    refine ⟨37053892672226497359176071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49405190229635329812234761 37053892672226497359176071)
    ·
      refine ⟨55580839008339746038764107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37053892672226497359176071 55580839008339746038764107)
      ·
        refine ⟨83371258512509619058146161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55580839008339746038764107 83371258512509619058146161)
        ·
          refine ⟨62528443884382214293609621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83371258512509619058146161 62528443884382214293609621)
          ·
            refine ⟨2931020807080416295012951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62528443884382214293609621 2931020807080416295012951)
            ·
              refine ⟨4396531210620624442519427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931020807080416295012951 4396531210620624442519427)
              ·
                refine ⟨6594796815930936663779141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396531210620624442519427 6594796815930936663779141)
                ·
                  refine ⟨1236524402987050624458589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6594796815930936663779141 1236524402987050624458589)
                  ·
                    refine ⟨463696651120143984171971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236524402987050624458589 463696651120143984171971)
                    ·
                      rfl

theorem cell22_1354569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_1354569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354569 prefixEnd_1354569 := by exact prefixLift 1354569
  have htrace : WordTrace (prefixWord ++ tailWord_1354569) baseStart_1354569 baseEnd_1354569 := by
    simpa [prefixWord, tailWord_1354569, baseEnd_1354569] using wordTrace_append hprefix tailTrace_1354569
  have hstable : (prefixWord ++ tailWord_1354569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354569).length < 2 ^ (prefixWord ++ tailWord_1354569).sum := by decide
  have hdescent : baseEnd_1354569 < baseStart_1354569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354599 : List Nat := [1, 1, 5, 1, 2, 2, 4, 6]
def baseStart_1354599 : Nat := 118140960795 + 1354599 * 2 ^ 59
def prefixEnd_1354599 : Nat := 4983230072969 + 3 ^ 40 * 1354599 * 2
def baseEnd_1354599 : Nat := 51522991192581545102431

theorem tailTrace_1354599 : CollatzResearch.WordTrace tailWord_1354599 prefixEnd_1354599 51522991192581545102431 := by
  unfold tailWord_1354599
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406284419526644935826851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32937522946351096623884567 49406284419526644935826851)
  ·
    refine ⟨74109426629289967403740277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49406284419526644935826851 74109426629289967403740277)
    ·
      refine ⟨6947758746495934444100651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74109426629289967403740277 6947758746495934444100651)
      ·
        refine ⟨10421638119743901666150977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947758746495934444100651 10421638119743901666150977)
        ·
          refine ⟨7816228589807926249613233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10421638119743901666150977 7816228589807926249613233)
          ·
            refine ⟨5862171442355944687209925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7816228589807926249613233 5862171442355944687209925)
            ·
              refine ⟨1099157145441739628851861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5862171442355944687209925 1099157145441739628851861)
              ·
                refine ⟨51522991192581545102431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1099157145441739628851861 51522991192581545102431)
                ·
                  rfl

theorem cell22_1354599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 6].length) (baseStart_1354599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354599 prefixEnd_1354599 := by exact prefixLift 1354599
  have htrace : WordTrace (prefixWord ++ tailWord_1354599) baseStart_1354599 baseEnd_1354599 := by
    simpa [prefixWord, tailWord_1354599, baseEnd_1354599] using wordTrace_append hprefix tailTrace_1354599
  have hstable : (prefixWord ++ tailWord_1354599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354599).length < 2 ^ (prefixWord ++ tailWord_1354599).sum := by decide
  have hdescent : baseEnd_1354599 < baseStart_1354599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354627 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 7]
def baseStart_1354627 : Nat := 118140960795 + 1354627 * 2 ^ 59
def prefixEnd_1354627 : Nat := 4983230072969 + 3 ^ 40 * 1354627 * 2
def baseEnd_1354627 : Nat := 154572168568483722073931

theorem tailTrace_1354627 : CollatzResearch.WordTrace tailWord_1354627 prefixEnd_1354627 154572168568483722073931 := by
  unfold tailWord_1354627
  simp only [CollatzResearch.WordTrace]
  refine ⟨49407305663425205717846135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32938203775616803811897423 49407305663425205717846135)
  ·
    refine ⟨74110958495137808576769203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49407305663425205717846135 74110958495137808576769203)
    ·
      refine ⟨111166437742706712865153805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74110958495137808576769203 111166437742706712865153805)
      ·
        refine ⟨41687414153515017324432677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111166437742706712865153805 41687414153515017324432677)
        ·
          refine ⟨7816390153784065748331127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41687414153515017324432677 7816390153784065748331127)
          ·
            refine ⟨11724585230676098622496691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816390153784065748331127 11724585230676098622496691)
            ·
              refine ⟨17586877846014147933745037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724585230676098622496691 17586877846014147933745037)
              ·
                refine ⟨6595079192255305475154389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17586877846014147933745037 6595079192255305475154389)
                ·
                  refine ⟨154572168568483722073931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6595079192255305475154389 154572168568483722073931)
                  ·
                    rfl

theorem cell22_1354627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_1354627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354627 prefixEnd_1354627 := by exact prefixLift 1354627
  have htrace : WordTrace (prefixWord ++ tailWord_1354627) baseStart_1354627 baseEnd_1354627 := by
    simpa [prefixWord, tailWord_1354627, baseEnd_1354627] using wordTrace_append hprefix tailTrace_1354627
  have hstable : (prefixWord ++ tailWord_1354627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354627).length < 2 ^ (prefixWord ++ tailWord_1354627).sum := by decide
  have hdescent : baseEnd_1354627 < baseStart_1354627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354631 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1354631 : Nat := 118140960795 + 1354631 * 2 ^ 59
def prefixEnd_1354631 : Nat := 4983230072969 + 3 ^ 40 * 1354631 * 2
def baseEnd_1354631 : Nat := 463717874987196489121781

theorem tailTrace_1354631 : CollatzResearch.WordTrace tailWord_1354631 prefixEnd_1354631 463717874987196489121781 := by
  unfold tailWord_1354631
  simp only [CollatzResearch.WordTrace]
  refine ⟨49407451555410714400991747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32938301036940476267327831 49407451555410714400991747)
  ·
    refine ⟨74111177333116071601487621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49407451555410714400991747 74111177333116071601487621)
    ·
      refine ⟨13895845749959263425278929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74111177333116071601487621 13895845749959263425278929)
      ·
        refine ⟨10421884312469447568959197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13895845749959263425278929 10421884312469447568959197)
        ·
          refine ⟨3908206617176042838359699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10421884312469447568959197 3908206617176042838359699)
          ·
            refine ⟨5862309925764064257539549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908206617176042838359699 5862309925764064257539549)
            ·
              refine ⟨2198366222161524096577331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5862309925764064257539549 2198366222161524096577331)
              ·
                refine ⟨3297549333242286144865997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198366222161524096577331 3297549333242286144865997)
                ·
                  refine ⟨1236580999965857304324749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3297549333242286144865997 1236580999965857304324749)
                  ·
                    refine ⟨463717874987196489121781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236580999965857304324749 463717874987196489121781)
                    ·
                      rfl

theorem cell22_1354631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1354631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354631 prefixEnd_1354631 := by exact prefixLift 1354631
  have htrace : WordTrace (prefixWord ++ tailWord_1354631) baseStart_1354631 baseEnd_1354631 := by
    simpa [prefixWord, tailWord_1354631, baseEnd_1354631] using wordTrace_append hprefix tailTrace_1354631
  have hstable : (prefixWord ++ tailWord_1354631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354631).length < 2 ^ (prefixWord ++ tailWord_1354631).sum := by decide
  have hdescent : baseEnd_1354631 < baseStart_1354631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354704 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_1354704 : Nat := 118140960795 + 1354704 * 2 ^ 59
def prefixEnd_1354704 : Nat := 4983230072969 + 3 ^ 40 * 1354704 * 2
def baseEnd_1354704 : Nat := 463742864379048632046557

theorem tailTrace_1354704 : CollatzResearch.WordTrace tailWord_1354704 prefixEnd_1354704 463742864379048632046557 := by
  unfold tailWord_1354704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24705057042073123934199583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32940076056097498578932777 24705057042073123934199583)
  ·
    refine ⟨37057585563109685901299375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24705057042073123934199583 37057585563109685901299375)
    ·
      refine ⟨55586378344664528851949063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37057585563109685901299375 55586378344664528851949063)
      ·
        refine ⟨83379567516996793277923595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55586378344664528851949063 83379567516996793277923595)
        ·
          refine ⟨125069351275495189916885393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83379567516996793277923595 125069351275495189916885393)
          ·
            refine ⟨93802013456621392437664045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125069351275495189916885393 93802013456621392437664045)
            ·
              refine ⟨35175755046233022164124017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93802013456621392437664045 35175755046233022164124017)
              ·
                refine ⟨26381816284674766623093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35175755046233022164124017 26381816284674766623093013)
                ·
                  refine ⟨1236647638344129685457485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26381816284674766623093013 1236647638344129685457485)
                  ·
                    refine ⟨463742864379048632046557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236647638344129685457485 463742864379048632046557)
                    ·
                      rfl

theorem cell22_1354704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_1354704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354704 prefixEnd_1354704 := by exact prefixLift 1354704
  have htrace : WordTrace (prefixWord ++ tailWord_1354704) baseStart_1354704 baseEnd_1354704 := by
    simpa [prefixWord, tailWord_1354704, baseEnd_1354704] using wordTrace_append hprefix tailTrace_1354704
  have hstable : (prefixWord ++ tailWord_1354704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354704).length < 2 ^ (prefixWord ++ tailWord_1354704).sum := by decide
  have hdescent : baseEnd_1354704 < baseStart_1354704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354706 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1354706 : Nat := 118140960795 + 1354706 * 2 ^ 59
def prefixEnd_1354706 : Nat := 4983230072969 + 3 ^ 40 * 1354706 * 2
def baseEnd_1354706 : Nat := 154581183006640431165517

theorem tailTrace_1354706 : CollatzResearch.WordTrace tailWord_1354706 prefixEnd_1354706 154581183006640431165517 := by
  unfold tailWord_1354706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12352546757534750552492993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32940124686759334806647981 12352546757534750552492993)
  ·
    refine ⟨9264410068151062914369745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12352546757534750552492993 9264410068151062914369745)
    ·
      refine ⟨6948307551113297185777309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9264410068151062914369745 6948307551113297185777309)
      ·
        refine ⟨2605615331667486444666491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6948307551113297185777309 2605615331667486444666491)
        ·
          refine ⟨3908422997501229666999737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605615331667486444666491 3908422997501229666999737)
          ·
            refine ⟨2931317248125922250249803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3908422997501229666999737 2931317248125922250249803)
            ·
              refine ⟨4396975872188883375374705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931317248125922250249803 4396975872188883375374705)
              ·
                refine ⟨3297731904141662531531029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396975872188883375374705 3297731904141662531531029)
                ·
                  refine ⟨154581183006640431165517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3297731904141662531531029 154581183006640431165517)
                  ·
                    rfl

theorem cell22_1354706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1354706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354706 prefixEnd_1354706 := by exact prefixLift 1354706
  have htrace : WordTrace (prefixWord ++ tailWord_1354706) baseStart_1354706 baseEnd_1354706 := by
    simpa [prefixWord, tailWord_1354706, baseEnd_1354706] using wordTrace_append hprefix tailTrace_1354706
  have hstable : (prefixWord ++ tailWord_1354706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354706).length < 2 ^ (prefixWord ++ tailWord_1354706).sum := by decide
  have hdescent : baseEnd_1354706 < baseStart_1354706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354800 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_1354800 : Nat := 118140960795 + 1354800 * 2 ^ 59
def prefixEnd_1354800 : Nat := 4983230072969 + 3 ^ 40 * 1354800 * 2
def baseEnd_1354800 : Nat := 463775727140936381646263

theorem tailTrace_1354800 : CollatzResearch.WordTrace tailWord_1354800 prefixEnd_1354800 463775727140936381646263 := by
  unfold tailWord_1354800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24706807745899228131946927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32942410327865637509262569 24706807745899228131946927)
  ·
    refine ⟨37060211618848842197920391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24706807745899228131946927 37060211618848842197920391)
    ·
      refine ⟨55590317428273263296880587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37060211618848842197920391 55590317428273263296880587)
      ·
        refine ⟨83385476142409894945320881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55590317428273263296880587 83385476142409894945320881)
        ·
          refine ⟨62539107106807421208990661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83385476142409894945320881 62539107106807421208990661)
          ·
            refine ⟨11726082582526391476685749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62539107106807421208990661 11726082582526391476685749)
            ·
              refine ⟨1099320242111849200939289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11726082582526391476685749 1099320242111849200939289)
              ·
                refine ⟨824490181583886900704467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099320242111849200939289 824490181583886900704467)
                ·
                  refine ⟨1236735272375830351056701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824490181583886900704467 1236735272375830351056701)
                  ·
                    refine ⟨463775727140936381646263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236735272375830351056701 463775727140936381646263)
                    ·
                      rfl

theorem cell22_1354800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_1354800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354800 prefixEnd_1354800 := by exact prefixLift 1354800
  have htrace : WordTrace (prefixWord ++ tailWord_1354800) baseStart_1354800 baseEnd_1354800 := by
    simpa [prefixWord, tailWord_1354800, baseEnd_1354800] using wordTrace_append hprefix tailTrace_1354800
  have hstable : (prefixWord ++ tailWord_1354800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354800).length < 2 ^ (prefixWord ++ tailWord_1354800).sum := by decide
  have hdescent : baseEnd_1354800 < baseStart_1354800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354813 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1354813 : Nat := 118140960795 + 1354813 * 2 ^ 59
def prefixEnd_1354813 : Nat := 4983230072969 + 3 ^ 40 * 1354813 * 2
def baseEnd_1354813 : Nat := 154593392435536227023741

theorem tailTrace_1354813 : CollatzResearch.WordTrace tailWord_1354813 prefixEnd_1354813 154593392435536227023741 := by
  unfold tailWord_1354813
  simp only [CollatzResearch.WordTrace]
  refine ⟨49414089640751359484117093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32942726427167572989411395 49414089640751359484117093)
  ·
    refine ⟨9265141807640879903271955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49414089640751359484117093 9265141807640879903271955)
    ·
      refine ⟨13897712711461319854907933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265141807640879903271955 13897712711461319854907933)
      ·
        refine ⟨5211642266797994945590475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13897712711461319854907933 5211642266797994945590475)
        ·
          refine ⟨7817463400196992418385713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211642266797994945590475 7817463400196992418385713)
          ·
            refine ⟨5863097550147744313789285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7817463400196992418385713 5863097550147744313789285)
            ·
              refine ⟨1099330790652702058835491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5863097550147744313789285 1099330790652702058835491)
              ·
                refine ⟨1648996185979053088253237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099330790652702058835491 1648996185979053088253237)
                ·
                  refine ⟨154593392435536227023741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1648996185979053088253237 154593392435536227023741)
                  ·
                    rfl

theorem cell22_1354813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1354813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354813 prefixEnd_1354813 := by exact prefixLift 1354813
  have htrace : WordTrace (prefixWord ++ tailWord_1354813) baseStart_1354813 baseEnd_1354813 := by
    simpa [prefixWord, tailWord_1354813, baseEnd_1354813] using wordTrace_append hprefix tailTrace_1354813
  have hstable : (prefixWord ++ tailWord_1354813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354813).length < 2 ^ (prefixWord ++ tailWord_1354813).sum := by decide
  have hdescent : baseEnd_1354813 < baseStart_1354813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354824 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_1354824 : Nat := 118140960795 + 1354824 * 2 ^ 59
def prefixEnd_1354824 : Nat := 4983230072969 + 3 ^ 40 * 1354824 * 2
def baseEnd_1354824 : Nat := 154594647610469439682063

theorem tailTrace_1354824 : CollatzResearch.WordTrace tailWord_1354824 prefixEnd_1354824 154594647610469439682063 := by
  unfold tailWord_1354824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707245421855754181383763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32942993895807672241845017 24707245421855754181383763)
  ·
    refine ⟨37060868132783631272075645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24707245421855754181383763 37060868132783631272075645)
    ·
      refine ⟨13897825549793861727028367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37060868132783631272075645 13897825549793861727028367)
      ·
        refine ⟨20846738324690792590542551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13897825549793861727028367 20846738324690792590542551)
        ·
          refine ⟨31270107487036188885813827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20846738324690792590542551 31270107487036188885813827)
          ·
            refine ⟨46905161230554283328720741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31270107487036188885813827 46905161230554283328720741)
            ·
              refine ⟨8794717730728928124135139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46905161230554283328720741 8794717730728928124135139)
              ·
                refine ⟨13192076596093392186202709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8794717730728928124135139 13192076596093392186202709)
                ·
                  refine ⟨154594647610469439682063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13192076596093392186202709 154594647610469439682063)
                  ·
                    rfl

theorem cell22_1354824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_1354824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354824 prefixEnd_1354824 := by exact prefixLift 1354824
  have htrace : WordTrace (prefixWord ++ tailWord_1354824) baseStart_1354824 baseEnd_1354824 := by
    simpa [prefixWord, tailWord_1354824, baseEnd_1354824] using wordTrace_append hprefix tailTrace_1354824
  have hstable : (prefixWord ++ tailWord_1354824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354824).length < 2 ^ (prefixWord ++ tailWord_1354824).sum := by decide
  have hdescent : baseEnd_1354824 < baseStart_1354824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354873 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_1354873 : Nat := 118140960795 + 1354873 * 2 ^ 59
def prefixEnd_1354873 : Nat := 4983230072969 + 3 ^ 40 * 1354873 * 2
def baseEnd_1354873 : Nat := 463800716532788524571039

theorem tailTrace_1354873 : CollatzResearch.WordTrace tailWord_1354873 prefixEnd_1354873 463800716532788524571039 := by
  unfold tailWord_1354873
  simp only [CollatzResearch.WordTrace]
  refine ⟨49416278020533989731301273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32944185347022659820867515 49416278020533989731301273)
  ·
    refine ⟨37062208515400492298475955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49416278020533989731301273 37062208515400492298475955)
    ·
      refine ⟨55593312773100738447713933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37062208515400492298475955 55593312773100738447713933)
      ·
        refine ⟨20847492289912776917892725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55593312773100738447713933 20847492289912776917892725)
        ·
          refine ⟨1954452402179322836052443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20847492289912776917892725 1954452402179322836052443)
          ·
            refine ⟨2931678603268984254078665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954452402179322836052443 2931678603268984254078665)
            ·
              refine ⟨2198758952451738190558999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931678603268984254078665 2198758952451738190558999)
              ·
                refine ⟨3298138428677607285838499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198758952451738190558999 3298138428677607285838499)
                ·
                  refine ⟨4947207643016410928757749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298138428677607285838499 4947207643016410928757749)
                  ·
                    refine ⟨463800716532788524571039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947207643016410928757749 463800716532788524571039)
                    ·
                      rfl

theorem cell22_1354873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_1354873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354873 prefixEnd_1354873 := by exact prefixLift 1354873
  have htrace : WordTrace (prefixWord ++ tailWord_1354873) baseStart_1354873 baseEnd_1354873 := by
    simpa [prefixWord, tailWord_1354873, baseEnd_1354873] using wordTrace_append hprefix tailTrace_1354873
  have hstable : (prefixWord ++ tailWord_1354873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354873).length < 2 ^ (prefixWord ++ tailWord_1354873).sum := by decide
  have hdescent : baseEnd_1354873 < baseStart_1354873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354888 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1354888 : Nat := 118140960795 + 1354888 * 2 ^ 59
def prefixEnd_1354888 : Nat := 4983230072969 + 3 ^ 40 * 1354888 * 2
def baseEnd_1354888 : Nat := 463805851339333485445993

theorem tailTrace_1354888 : CollatzResearch.WordTrace tailWord_1354888 prefixEnd_1354888 463805851339333485445993 := by
  unfold tailWord_1354888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708412557739823646548659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32944550076986431528731545 24708412557739823646548659)
  ·
    refine ⟨37062618836609735469822989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24708412557739823646548659 37062618836609735469822989)
    ·
      refine ⟨13898482063728650801183621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37062618836609735469822989 13898482063728650801183621)
      ·
        refine ⟨2605965386949122025221929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13898482063728650801183621 2605965386949122025221929)
        ·
          refine ⟨1954474040211841518916447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605965386949122025221929 1954474040211841518916447)
          ·
            refine ⟨2931711060317762278374671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954474040211841518916447 2931711060317762278374671)
            ·
              refine ⟨4397566590476643417562007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931711060317762278374671 4397566590476643417562007)
              ·
                refine ⟨6596349885714965126343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397566590476643417562007 6596349885714965126343011)
                ·
                  refine ⟨9894524828572447689514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596349885714965126343011 9894524828572447689514517)
                  ·
                    refine ⟨463805851339333485445993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9894524828572447689514517 463805851339333485445993)
                    ·
                      rfl

theorem cell22_1354888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1354888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354888 prefixEnd_1354888 := by exact prefixLift 1354888
  have htrace : WordTrace (prefixWord ++ tailWord_1354888) baseStart_1354888 baseEnd_1354888 := by
    simpa [prefixWord, tailWord_1354888, baseEnd_1354888] using wordTrace_append hprefix tailTrace_1354888
  have hstable : (prefixWord ++ tailWord_1354888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354888).length < 2 ^ (prefixWord ++ tailWord_1354888).sum := by decide
  have hdescent : baseEnd_1354888 < baseStart_1354888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354931 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 5]
def baseStart_1354931 : Nat := 118140960795 + 1354931 * 2 ^ 59
def prefixEnd_1354931 : Nat := 4983230072969 + 3 ^ 40 * 1354931 * 2
def baseEnd_1354931 : Nat := 154606857039365235540287

theorem tailTrace_1354931 : CollatzResearch.WordTrace tailWord_1354931 prefixEnd_1354931 154606857039365235540287 := by
  unfold tailWord_1354931
  simp only [CollatzResearch.WordTrace]
  refine ⟨49418393454323865636912647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32945595636215910424608431 49418393454323865636912647)
  ·
    refine ⟨74127590181485798455368971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49418393454323865636912647 74127590181485798455368971)
    ·
      refine ⟨111191385272228697683053457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74127590181485798455368971 111191385272228697683053457)
      ·
        refine ⟨83393538954171523262290093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111191385272228697683053457 83393538954171523262290093)
        ·
          refine ⟨31272577107814321223358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83393538954171523262290093 31272577107814321223358785)
          ·
            refine ⟨23454432830860740917519089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31272577107814321223358785 23454432830860740917519089)
            ·
              refine ⟨17590824623145555688139317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23454432830860740917519089 17590824623145555688139317)
              ·
                refine ⟨1649139808419895845763061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17590824623145555688139317 1649139808419895845763061)
                ·
                  refine ⟨154606857039365235540287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649139808419895845763061 154606857039365235540287)
                  ·
                    rfl

theorem cell22_1354931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].length) (baseStart_1354931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354931 prefixEnd_1354931 := by exact prefixLift 1354931
  have htrace : WordTrace (prefixWord ++ tailWord_1354931) baseStart_1354931 baseEnd_1354931 := by
    simpa [prefixWord, tailWord_1354931, baseEnd_1354931] using wordTrace_append hprefix tailTrace_1354931
  have hstable : (prefixWord ++ tailWord_1354931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354931).length < 2 ^ (prefixWord ++ tailWord_1354931).sum := by decide
  have hdescent : baseEnd_1354931 < baseStart_1354931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354961 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_1354961 : Nat := 118140960795 + 1354961 * 2 ^ 59
def prefixEnd_1354961 : Nat := 4983230072969 + 3 ^ 40 * 1354961 * 2
def baseEnd_1354961 : Nat := 463830840731185628370769

theorem tailTrace_1354961 : CollatzResearch.WordTrace tailWord_1354961 prefixEnd_1354961 463830840731185628370769 := by
  unfold tailWord_1354961
  simp only [CollatzResearch.WordTrace]
  refine ⟨49419487644215180760504737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32946325096143453840336491 49419487644215180760504737)
  ·
    refine ⟨37064615733161385570378553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49419487644215180760504737 37064615733161385570378553)
    ·
      refine ⟨27798461799871039177783915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37064615733161385570378553 27798461799871039177783915)
      ·
        refine ⟨41697692699806558766675873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27798461799871039177783915 41697692699806558766675873)
        ·
          refine ⟨31273269524854919075006905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41697692699806558766675873 31273269524854919075006905)
          ·
            refine ⟨23454952143641189306255179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31273269524854919075006905 23454952143641189306255179)
            ·
              refine ⟨35182428215461783959382769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23454952143641189306255179 35182428215461783959382769)
              ·
                refine ⟨26386821161596337969537077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35182428215461783959382769 26386821161596337969537077)
                ·
                  refine ⟨2473764483899656684644101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26386821161596337969537077 2473764483899656684644101)
                  ·
                    refine ⟨463830840731185628370769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473764483899656684644101 463830840731185628370769)
                    ·
                      rfl

theorem cell22_1354961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_1354961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354961 prefixEnd_1354961 := by exact prefixLift 1354961
  have htrace : WordTrace (prefixWord ++ tailWord_1354961) baseStart_1354961 baseEnd_1354961 := by
    simpa [prefixWord, tailWord_1354961, baseEnd_1354961] using wordTrace_append hprefix tailTrace_1354961
  have hstable : (prefixWord ++ tailWord_1354961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354961).length < 2 ^ (prefixWord ++ tailWord_1354961).sum := by decide
  have hdescent : baseEnd_1354961 < baseStart_1354961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354995 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 1, 4]
def baseStart_1354995 : Nat := 118140960795 + 1354995 * 2 ^ 59
def prefixEnd_1354995 : Nat := 4983230072969 + 3 ^ 40 * 1354995 * 2
def baseEnd_1354995 : Nat := 463842479626020873020665

theorem tailTrace_1354995 : CollatzResearch.WordTrace tailWord_1354995 prefixEnd_1354995 463842479626020873020665 := by
  unfold tailWord_1354995
  simp only [CollatzResearch.WordTrace]
  refine ⟨49420727726092004567242439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32947151817394669711494959 49420727726092004567242439)
  ·
    refine ⟨74131091589138006850863659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49420727726092004567242439 74131091589138006850863659)
    ·
      refine ⟨111196637383707010276295489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74131091589138006850863659 111196637383707010276295489)
      ·
        refine ⟨83397478037780257707221617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111196637383707010276295489 83397478037780257707221617)
        ·
          refine ⟨62548108528335193280416213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83397478037780257707221617 62548108528335193280416213)
          ·
            refine ⟨1465971293632856092509755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62548108528335193280416213 1465971293632856092509755)
            ·
              refine ⟨2198956940449284138764633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465971293632856092509755 2198956940449284138764633)
              ·
                refine ⟨1649217705336963104073475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198956940449284138764633 1649217705336963104073475)
                ·
                  refine ⟨2473826558005444656110213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649217705336963104073475 2473826558005444656110213)
                  ·
                    refine ⟨463842479626020873020665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473826558005444656110213 463842479626020873020665)
                    ·
                      rfl

theorem cell22_1354995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].length) (baseStart_1354995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1354995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1354995 prefixEnd_1354995 := by exact prefixLift 1354995
  have htrace : WordTrace (prefixWord ++ tailWord_1354995) baseStart_1354995 baseEnd_1354995 := by
    simpa [prefixWord, tailWord_1354995, baseEnd_1354995] using wordTrace_append hprefix tailTrace_1354995
  have hstable : (prefixWord ++ tailWord_1354995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354995).length < 2 ^ (prefixWord ++ tailWord_1354995).sum := by decide
  have hdescent : baseEnd_1354995 < baseStart_1354995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355012 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1355012 : Nat := 118140960795 + 1355012 * 2 ^ 59
def prefixEnd_1355012 : Nat := 4983230072969 + 3 ^ 40 * 1355012 * 2
def baseEnd_1355012 : Nat := 463848299073438495345613

theorem tailTrace_1355012 : CollatzResearch.WordTrace tailWord_1355012 prefixEnd_1355012 463848299073438495345613 := by
  unfold tailWord_1355012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24710673883515208235305645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32947565178020277647074193 24710673883515208235305645)
  ·
    refine ⟨9266502706318203088239617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24710673883515208235305645 9266502706318203088239617)
    ·
      refine ⟨6949877029738652316179713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9266502706318203088239617 6949877029738652316179713)
      ·
        refine ⟨5212407772303989237134785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6949877029738652316179713 5212407772303989237134785)
        ·
          refine ⟨3909305829227991927851089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5212407772303989237134785 3909305829227991927851089)
          ·
            refine ⟨2931979371920993945888317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909305829227991927851089 2931979371920993945888317)
            ·
              refine ⟨1099492264470372729708119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2931979371920993945888317 1099492264470372729708119)
              ·
                refine ⟨1649238396705559094562179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099492264470372729708119 1649238396705559094562179)
                ·
                  refine ⟨2473857595058338641843269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649238396705559094562179 2473857595058338641843269)
                  ·
                    refine ⟨463848299073438495345613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473857595058338641843269 463848299073438495345613)
                    ·
                      rfl

theorem cell22_1355012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1355012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355012 prefixEnd_1355012 := by exact prefixLift 1355012
  have htrace : WordTrace (prefixWord ++ tailWord_1355012) baseStart_1355012 baseEnd_1355012 := by
    simpa [prefixWord, tailWord_1355012, baseEnd_1355012] using wordTrace_append hprefix tailTrace_1355012
  have hstable : (prefixWord ++ tailWord_1355012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355012).length < 2 ^ (prefixWord ++ tailWord_1355012).sum := by decide
  have hdescent : baseEnd_1355012 < baseStart_1355012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355025 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1355025 : Nat := 118140960795 + 1355025 * 2 ^ 59
def prefixEnd_1355025 : Nat := 4983230072969 + 3 ^ 40 * 1355025 * 2
def baseEnd_1355025 : Nat := 463852749239110794770573

theorem tailTrace_1355025 : CollatzResearch.WordTrace tailWord_1355025 prefixEnd_1355025 463852749239110794770573 := by
  unfold tailWord_1355025
  simp only [CollatzResearch.WordTrace]
  refine ⟨49421821915983319690834529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32947881277322213127223019 49421821915983319690834529)
  ·
    refine ⟨37066366436987489768125897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49421821915983319690834529 37066366436987489768125897)
    ·
      refine ⟨27799774827740617326094423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37066366436987489768125897 27799774827740617326094423)
      ·
        refine ⟨41699662241610925989141635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27799774827740617326094423 41699662241610925989141635)
        ·
          refine ⟨62549493362416388983712453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41699662241610925989141635 62549493362416388983712453)
          ·
            refine ⟨11728030005453072934446085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62549493362416388983712453 11728030005453072934446085)
            ·
              refine ⟨2199005626022451175208641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11728030005453072934446085 2199005626022451175208641)
              ·
                refine ⟨1649254219516838381406481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199005626022451175208641 1649254219516838381406481)
                ·
                  refine ⟨1236940664637628786054861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649254219516838381406481 1236940664637628786054861)
                  ·
                    refine ⟨463852749239110794770573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236940664637628786054861 463852749239110794770573)
                    ·
                      rfl

theorem cell22_1355025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1355025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355025 prefixEnd_1355025 := by exact prefixLift 1355025
  have htrace : WordTrace (prefixWord ++ tailWord_1355025) baseStart_1355025 baseEnd_1355025 := by
    simpa [prefixWord, tailWord_1355025, baseEnd_1355025] using wordTrace_append hprefix tailTrace_1355025
  have hstable : (prefixWord ++ tailWord_1355025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355025).length < 2 ^ (prefixWord ++ tailWord_1355025).sum := by decide
  have hdescent : baseEnd_1355025 < baseStart_1355025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355070 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1355070 : Nat := 118140960795 + 1355070 * 2 ^ 59
def prefixEnd_1355070 : Nat := 4983230072969 + 3 ^ 40 * 1355070 * 2
def baseEnd_1355070 : Nat := 463868153658745677395435

theorem tailTrace_1355070 : CollatzResearch.WordTrace tailWord_1355070 prefixEnd_1355070 463868153658745677395435 := by
  unfold tailWord_1355070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177932900102536547027833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32948975467213528250815109 6177932900102536547027833)
  ·
    refine ⟨4633449675076902410270875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6177932900102536547027833 4633449675076902410270875)
    ·
      refine ⟨6950174512615353615406313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633449675076902410270875 6950174512615353615406313)
      ·
        refine ⟨5212630884461515211554735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950174512615353615406313 5212630884461515211554735)
        ·
          refine ⟨7818946326692272817332103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212630884461515211554735 7818946326692272817332103)
          ·
            refine ⟨11728419490038409225998155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7818946326692272817332103 11728419490038409225998155)
            ·
              refine ⟨17592629235057613838997233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11728419490038409225998155 17592629235057613838997233)
              ·
                refine ⟨13194471926293210379247925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17592629235057613838997233 13194471926293210379247925)
                ·
                  refine ⟨1236981743089988473054493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13194471926293210379247925 1236981743089988473054493)
                  ·
                    refine ⟨463868153658745677395435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236981743089988473054493 463868153658745677395435)
                    ·
                      rfl

theorem cell22_1355070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1355070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355070 prefixEnd_1355070 := by exact prefixLift 1355070
  have htrace : WordTrace (prefixWord ++ tailWord_1355070) baseStart_1355070 baseEnd_1355070 := by
    simpa [prefixWord, tailWord_1355070, baseEnd_1355070] using wordTrace_append hprefix tailTrace_1355070
  have hstable : (prefixWord ++ tailWord_1355070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355070).length < 2 ^ (prefixWord ++ tailWord_1355070).sum := by decide
  have hdescent : baseEnd_1355070 < baseStart_1355070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355098 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_1355098 : Nat := 118140960795 + 1355098 * 2 ^ 59
def prefixEnd_1355098 : Nat := 4983230072969 + 3 ^ 40 * 1355098 * 2
def baseEnd_1355098 : Nat := 463877738630962937695349

theorem tailTrace_1355098 : CollatzResearch.WordTrace tailWord_1355098 prefixEnd_1355098 463877738630962937695349 := by
  unfold tailWord_1355098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356121111179713289560487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32949656296479235438827965 12356121111179713289560487)
  ·
    refine ⟨18534181666769569934340731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356121111179713289560487 18534181666769569934340731)
    ·
      refine ⟨27801272500154354901511097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18534181666769569934340731 27801272500154354901511097)
      ·
        refine ⟨20850954375115766176133323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27801272500154354901511097 20850954375115766176133323)
        ·
          refine ⟨31276431562673649264199985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20850954375115766176133323 31276431562673649264199985)
          ·
            refine ⟨23457323672005236948149989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31276431562673649264199985 23457323672005236948149989)
            ·
              refine ⟨4398248188500981927778123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23457323672005236948149989 4398248188500981927778123)
              ·
                refine ⟨6597372282751472891667185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398248188500981927778123 6597372282751472891667185)
                ·
                  refine ⟨4948029212063604668750389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597372282751472891667185 4948029212063604668750389)
                  ·
                    refine ⟨463877738630962937695349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4948029212063604668750389 463877738630962937695349)
                    ·
                      rfl

theorem cell22_1355098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_1355098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355098 prefixEnd_1355098 := by exact prefixLift 1355098
  have htrace : WordTrace (prefixWord ++ tailWord_1355098) baseStart_1355098 baseEnd_1355098 := by
    simpa [prefixWord, tailWord_1355098, baseEnd_1355098] using wordTrace_append hprefix tailTrace_1355098
  have hstable : (prefixWord ++ tailWord_1355098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355098).length < 2 ^ (prefixWord ++ tailWord_1355098).sum := by decide
  have hdescent : baseEnd_1355098 < baseStart_1355098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355138 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1355138 : Nat := 118140960795 + 1355138 * 2 ^ 59
def prefixEnd_1355138 : Nat := 4983230072969 + 3 ^ 40 * 1355138 * 2
def baseEnd_1355138 : Nat := 463891431448416166695227

theorem tailTrace_1355138 : CollatzResearch.WordTrace tailWord_1355138 prefixEnd_1355138 463891431448416166695227 := by
  unfold tailWord_1355138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356485841143484997424517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32950628909715959993132045 12356485841143484997424517)
  ·
    refine ⟨2316841095214403437017097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12356485841143484997424517 2316841095214403437017097)
    ·
      refine ⟨1737630821410802577762823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2316841095214403437017097 1737630821410802577762823)
      ·
        refine ⟨2606446232116203866644235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737630821410802577762823 2606446232116203866644235)
        ·
          refine ⟨3909669348174305799966353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606446232116203866644235 3909669348174305799966353)
          ·
            refine ⟨2932252011130729349974765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909669348174305799966353 2932252011130729349974765)
            ·
              refine ⟨1099594504174023506240537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932252011130729349974765 1099594504174023506240537)
              ·
                refine ⟨824695878130517629680403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099594504174023506240537 824695878130517629680403)
                ·
                  refine ⟨1237043817195776444520605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824695878130517629680403 1237043817195776444520605)
                  ·
                    refine ⟨463891431448416166695227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237043817195776444520605 463891431448416166695227)
                    ·
                      rfl

theorem cell22_1355138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1355138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355138 prefixEnd_1355138 := by exact prefixLift 1355138
  have htrace : WordTrace (prefixWord ++ tailWord_1355138) baseStart_1355138 baseEnd_1355138 := by
    simpa [prefixWord, tailWord_1355138, baseEnd_1355138] using wordTrace_append hprefix tailTrace_1355138
  have hstable : (prefixWord ++ tailWord_1355138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355138).length < 2 ^ (prefixWord ++ tailWord_1355138).sum := by decide
  have hdescent : baseEnd_1355138 < baseStart_1355138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355196 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_1355196 : Nat := 118140960795 + 1355196 * 2 ^ 59
def prefixEnd_1355196 : Nat := 4983230072969 + 3 ^ 40 * 1355196 * 2
def baseEnd_1355196 : Nat := 154637095344574449581683

theorem tailTrace_1355196 : CollatzResearch.WordTrace tailWord_1355196 prefixEnd_1355196 154637095344574449581683 := by
  unfold tailWord_1355196
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714029399181907947654721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32952039198909210596872961 24714029399181907947654721)
  ·
    refine ⟨18535522049386430960741041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24714029399181907947654721 18535522049386430960741041)
    ·
      refine ⟨13901641537039823220555781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18535522049386430960741041 13901641537039823220555781)
      ·
        refine ⟨2606557788194966853854209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13901641537039823220555781 2606557788194966853854209)
        ·
          refine ⟨1954918341146225140390657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2606557788194966853854209 1954918341146225140390657)
          ·
            refine ⟨1466188755859668855292993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954918341146225140390657 1466188755859668855292993)
            ·
              refine ⟨1099641566894751641469745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466188755859668855292993 1099641566894751641469745)
              ·
                refine ⟨824731175171063731102309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099641566894751641469745 824731175171063731102309)
                ·
                  refine ⟨154637095344574449581683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824731175171063731102309 154637095344574449581683)
                  ·
                    rfl

theorem cell22_1355196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_1355196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355196 prefixEnd_1355196 := by exact prefixLift 1355196
  have htrace : WordTrace (prefixWord ++ tailWord_1355196) baseStart_1355196 baseEnd_1355196 := by
    simpa [prefixWord, tailWord_1355196, baseEnd_1355196] using wordTrace_append hprefix tailTrace_1355196
  have hstable : (prefixWord ++ tailWord_1355196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355196).length < 2 ^ (prefixWord ++ tailWord_1355196).sum := by decide
  have hdescent : baseEnd_1355196 < baseStart_1355196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355203 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_1355203 : Nat := 118140960795 + 1355203 * 2 ^ 59
def prefixEnd_1355203 : Nat := 4983230072969 + 3 ^ 40 * 1355203 * 2
def baseEnd_1355203 : Nat := 463913682276777663820027

theorem tailTrace_1355203 : CollatzResearch.WordTrace tailWord_1355203 prefixEnd_1355203 463913682276777663820027 := by
  unfold tailWord_1355203
  simp only [CollatzResearch.WordTrace]
  refine ⟨49428314109338456090814263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32952209406225637393876175 49428314109338456090814263)
  ·
    refine ⟨74142471164007684136221395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49428314109338456090814263 74142471164007684136221395)
    ·
      refine ⟨111213706746011526204332093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74142471164007684136221395 111213706746011526204332093)
      ·
        refine ⟨41705140029754322326624535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111213706746011526204332093 41705140029754322326624535)
        ·
          refine ⟨62557710044631483489936803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41705140029754322326624535 62557710044631483489936803)
          ·
            refine ⟨93836565066947225234905205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62557710044631483489936803 93836565066947225234905205)
            ·
              refine ⟨8797177975026302365772363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93836565066947225234905205 8797177975026302365772363)
              ·
                refine ⟨13195766962539453548658545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8797177975026302365772363 13195766962539453548658545)
                ·
                  refine ⟨9896825221904590161493909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13195766962539453548658545 9896825221904590161493909)
                  ·
                    refine ⟨463913682276777663820027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9896825221904590161493909 463913682276777663820027)
                    ·
                      rfl

theorem cell22_1355203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_1355203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355203 prefixEnd_1355203 := by exact prefixLift 1355203
  have htrace : WordTrace (prefixWord ++ tailWord_1355203) baseStart_1355203 baseEnd_1355203 := by
    simpa [prefixWord, tailWord_1355203, baseEnd_1355203] using wordTrace_append hprefix tailTrace_1355203
  have hstable : (prefixWord ++ tailWord_1355203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355203).length < 2 ^ (prefixWord ++ tailWord_1355203).sum := by decide
  have hdescent : baseEnd_1355203 < baseStart_1355203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355239 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1355239 : Nat := 118140960795 + 1355239 * 2 ^ 59
def prefixEnd_1355239 : Nat := 4983230072969 + 3 ^ 40 * 1355239 * 2
def baseEnd_1355239 : Nat := 463926005812485569919917

theorem tailTrace_1355239 : CollatzResearch.WordTrace tailWord_1355239 prefixEnd_1355239 463926005812485569919917 := by
  unfold tailWord_1355239
  simp only [CollatzResearch.WordTrace]
  refine ⟨49429627137208034239124771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32953084758138689492749847 49429627137208034239124771)
  ·
    refine ⟨74144440705812051358687157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49429627137208034239124771 74144440705812051358687157)
    ·
      refine ⟨6951041316169879814876921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74144440705812051358687157 6951041316169879814876921)
      ·
        refine ⟨5213280987127409861157691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6951041316169879814876921 5213280987127409861157691)
        ·
          refine ⟨7819921480691114791736537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213280987127409861157691 7819921480691114791736537)
          ·
            refine ⟨5864941110518336093802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7819921480691114791736537 5864941110518336093802403)
            ·
              refine ⟨8797411665777504140703605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864941110518336093802403 8797411665777504140703605)
              ·
                refine ⟨824757343666641013190963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8797411665777504140703605 824757343666641013190963)
                ·
                  refine ⟨1237136015499961519786445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824757343666641013190963 1237136015499961519786445)
                  ·
                    refine ⟨463926005812485569919917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237136015499961519786445 463926005812485569919917)
                    ·
                      rfl

theorem cell22_1355239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1355239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355239 prefixEnd_1355239 := by exact prefixLift 1355239
  have htrace : WordTrace (prefixWord ++ tailWord_1355239) baseStart_1355239 baseEnd_1355239 := by
    simpa [prefixWord, tailWord_1355239, baseEnd_1355239] using wordTrace_append hprefix tailTrace_1355239
  have hstable : (prefixWord ++ tailWord_1355239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355239).length < 2 ^ (prefixWord ++ tailWord_1355239).sum := by decide
  have hdescent : baseEnd_1355239 < baseStart_1355239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355295 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_1355295 : Nat := 118140960795 + 1355295 * 2 ^ 59
def prefixEnd_1355295 : Nat := 4983230072969 + 3 ^ 40 * 1355295 * 2
def baseEnd_1355295 : Nat := 463945175756920090519745

theorem tailTrace_1355295 : CollatzResearch.WordTrace tailWord_1355295 prefixEnd_1355295 463945175756920090519745 := by
  unfold tailWord_1355295
  simp only [CollatzResearch.WordTrace]
  refine ⟨49431669625005155803163339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32954446416670103868775559 49431669625005155803163339)
  ·
    refine ⟨74147504437507733704745009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49431669625005155803163339 74147504437507733704745009)
    ·
      refine ⟨55610628328130800278558757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74147504437507733704745009 55610628328130800278558757)
      ·
        refine ⟨10426992811524525052229767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55610628328130800278558757 10426992811524525052229767)
        ·
          refine ⟨15640489217286787578344651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426992811524525052229767 15640489217286787578344651)
          ·
            refine ⟨23460733825930181367516977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15640489217286787578344651 23460733825930181367516977)
            ·
              refine ⟨17595550369447636025637733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23460733825930181367516977 17595550369447636025637733)
              ·
                refine ⟨3299165694271431754807075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17595550369447636025637733 3299165694271431754807075)
                ·
                  refine ⟨4948748541407147632210613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299165694271431754807075 4948748541407147632210613)
                  ·
                    refine ⟨463945175756920090519745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4948748541407147632210613 463945175756920090519745)
                    ·
                      rfl

theorem cell22_1355295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_1355295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355295 prefixEnd_1355295 := by exact prefixLift 1355295
  have htrace : WordTrace (prefixWord ++ tailWord_1355295) baseStart_1355295 baseEnd_1355295 := by
    simpa [prefixWord, tailWord_1355295, baseEnd_1355295] using wordTrace_append hprefix tailTrace_1355295
  have hstable : (prefixWord ++ tailWord_1355295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355295).length < 2 ^ (prefixWord ++ tailWord_1355295).sum := by decide
  have hdescent : baseEnd_1355295 < baseStart_1355295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355312 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_1355312 : Nat := 118140960795 + 1355312 * 2 ^ 59
def prefixEnd_1355312 : Nat := 4983230072969 + 3 ^ 40 * 1355312 * 2
def baseEnd_1355312 : Nat := 463950995204337712844693

theorem tailTrace_1355312 : CollatzResearch.WordTrace tailWord_1355312 prefixEnd_1355312 463950995204337712844693 := by
  unfold tailWord_1355312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716144832971783853266095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32954859777295711804354793 24716144832971783853266095)
  ·
    refine ⟨37074217249457675779899143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24716144832971783853266095 37074217249457675779899143)
    ·
      refine ⟨55611325874186513669848715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37074217249457675779899143 55611325874186513669848715)
      ·
        refine ⟨83416988811279770504773073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55611325874186513669848715 83416988811279770504773073)
        ·
          refine ⟨62562741608459827878579805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83416988811279770504773073 62562741608459827878579805)
          ·
            refine ⟨23461028103172435454467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62562741608459827878579805 23461028103172435454467427)
            ·
              refine ⟨35191542154758653181701141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23461028103172435454467427 35191542154758653181701141)
              ·
                refine ⟨1649603538504311867892241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35191542154758653181701141 1649603538504311867892241)
                ·
                  refine ⟨1237202653878233900919181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649603538504311867892241 1237202653878233900919181)
                  ·
                    refine ⟨463950995204337712844693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237202653878233900919181 463950995204337712844693)
                    ·
                      rfl

theorem cell22_1355312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_1355312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355312 prefixEnd_1355312 := by exact prefixLift 1355312
  have htrace : WordTrace (prefixWord ++ tailWord_1355312) baseStart_1355312 baseEnd_1355312 := by
    simpa [prefixWord, tailWord_1355312, baseEnd_1355312] using wordTrace_append hprefix tailTrace_1355312
  have hstable : (prefixWord ++ tailWord_1355312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355312).length < 2 ^ (prefixWord ++ tailWord_1355312).sum := by decide
  have hdescent : baseEnd_1355312 < baseStart_1355312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355329 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1355329 : Nat := 118140960795 + 1355329 * 2 ^ 59
def prefixEnd_1355329 : Nat := 4983230072969 + 3 ^ 40 * 1355329 * 2
def baseEnd_1355329 : Nat := 463956814651755335169641

theorem tailTrace_1355329 : CollatzResearch.WordTrace tailWord_1355329 prefixEnd_1355329 463956814651755335169641 := by
  unfold tailWord_1355329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49432909706881979609901041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32955273137921319739934027 49432909706881979609901041)
  ·
    refine ⟨37074682280161484707425781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49432909706881979609901041 37074682280161484707425781)
    ·
      refine ⟨3475751463765139191321167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37074682280161484707425781 3475751463765139191321167)
      ·
        refine ⟨5213627195647708786981751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475751463765139191321167 5213627195647708786981751)
        ·
          refine ⟨7820440793471563180472627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213627195647708786981751 7820440793471563180472627)
          ·
            refine ⟨11730661190207344770708941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820440793471563180472627 11730661190207344770708941)
            ·
              refine ⟨4398997946327754289015853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11730661190207344770708941 4398997946327754289015853)
              ·
                refine ⟨1649624229872907858380945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4398997946327754289015853 1649624229872907858380945)
                ·
                  refine ⟨1237218172404680893785709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649624229872907858380945 1237218172404680893785709)
                  ·
                    refine ⟨463956814651755335169641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237218172404680893785709 463956814651755335169641)
                    ·
                      rfl

theorem cell22_1355329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1355329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355329 prefixEnd_1355329 := by exact prefixLift 1355329
  have htrace : WordTrace (prefixWord ++ tailWord_1355329) baseStart_1355329 baseEnd_1355329 := by
    simpa [prefixWord, tailWord_1355329, baseEnd_1355329] using wordTrace_append hprefix tailTrace_1355329
  have hstable : (prefixWord ++ tailWord_1355329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355329).length < 2 ^ (prefixWord ++ tailWord_1355329).sum := by decide
  have hdescent : baseEnd_1355329 < baseStart_1355329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355350 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1355350 : Nat := 118140960795 + 1355350 * 2 ^ 59
def prefixEnd_1355350 : Nat := 4983230072969 + 3 ^ 40 * 1355350 * 2
def baseEnd_1355350 : Nat := 463964003380918280394577

theorem tailTrace_1355350 : CollatzResearch.WordTrace tailWord_1355350 prefixEnd_1355350 463964003380918280394577 := by
  unfold tailWord_1355350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089604727487868762275969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32955783759870600130943669 3089604727487868762275969)
  ·
    refine ⟨2317203545615901571706977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3089604727487868762275969 2317203545615901571706977)
    ·
      refine ⟨1737902659211926178780233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317203545615901571706977 1737902659211926178780233)
      ·
        refine ⟨1303426994408944634085175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1737902659211926178780233 1303426994408944634085175)
        ·
          refine ⟨1955140491613416951127763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303426994408944634085175 1955140491613416951127763)
          ·
            refine ⟨2932710737420125426691645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955140491613416951127763 2932710737420125426691645)
            ·
              refine ⟨1099766526532547035009367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932710737420125426691645 1099766526532547035009367)
              ·
                refine ⟨1649649789798820552514051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099766526532547035009367 1649649789798820552514051)
                ·
                  refine ⟨2474474684698230828771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649649789798820552514051 2474474684698230828771077)
                  ·
                    refine ⟨463964003380918280394577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474474684698230828771077 463964003380918280394577)
                    ·
                      rfl

theorem cell22_1355350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1355350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355350 prefixEnd_1355350 := by exact prefixLift 1355350
  have htrace : WordTrace (prefixWord ++ tailWord_1355350) baseStart_1355350 baseEnd_1355350 := by
    simpa [prefixWord, tailWord_1355350, baseEnd_1355350] using wordTrace_append hprefix tailTrace_1355350
  have hstable : (prefixWord ++ tailWord_1355350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355350).length < 2 ^ (prefixWord ++ tailWord_1355350).sum := by decide
  have hdescent : baseEnd_1355350 < baseStart_1355350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355438 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1355438 : Nat := 118140960795 + 1355438 * 2 ^ 59
def prefixEnd_1355438 : Nat := 4983230072969 + 3 ^ 40 * 1355438 * 2
def baseEnd_1355438 : Nat := 154664709193105128064769

theorem tailTrace_1355438 : CollatzResearch.WordTrace tailWord_1355438 prefixEnd_1355438 154664709193105128064769 := by
  unfold tailWord_1355438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179610657935886403202371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32957923508991394150412645 6179610657935886403202371)
  ·
    refine ⟨9269415986903829604803557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179610657935886403202371 9269415986903829604803557)
    ·
      refine ⟨1738015497544468050900667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9269415986903829604803557 1738015497544468050900667)
      ·
        refine ⟨2607023246316702076351001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738015497544468050900667 2607023246316702076351001)
        ·
          refine ⟨1955267434737526557263251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607023246316702076351001 1955267434737526557263251)
          ·
            refine ⟨2932901152106289835894877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955267434737526557263251 2932901152106289835894877)
            ·
              refine ⟨1099837932039858688460579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932901152106289835894877 1099837932039858688460579)
              ·
                refine ⟨1649756898059788032690869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099837932039858688460579 1649756898059788032690869)
                ·
                  refine ⟨154664709193105128064769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649756898059788032690869 154664709193105128064769)
                  ·
                    rfl

theorem cell22_1355438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1355438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355438 prefixEnd_1355438 := by exact prefixLift 1355438
  have htrace : WordTrace (prefixWord ++ tailWord_1355438) baseStart_1355438 baseEnd_1355438 := by
    simpa [prefixWord, tailWord_1355438, baseEnd_1355438] using wordTrace_append hprefix tailTrace_1355438
  have hstable : (prefixWord ++ tailWord_1355438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355438).length < 2 ^ (prefixWord ++ tailWord_1355438).sum := by decide
  have hdescent : baseEnd_1355438 < baseStart_1355438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355537 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_1355537 : Nat := 118140960795 + 1355537 * 2 ^ 59
def prefixEnd_1355537 : Nat := 4983230072969 + 3 ^ 40 * 1355537 * 2
def baseEnd_1355537 : Nat := 464028017302512125969003

theorem tailTrace_1355537 : CollatzResearch.WordTrace tailWord_1355537 prefixEnd_1355537 464028017302512125969003 := by
  unfold tailWord_1355537
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440496090128431133472865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32960330726752287422315243 49440496090128431133472865)
  ·
    refine ⟨37080372067596323350104649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49440496090128431133472865 37080372067596323350104649)
    ·
      refine ⟨27810279050697242512578487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37080372067596323350104649 27810279050697242512578487)
      ·
        refine ⟨41715418576045863768867731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27810279050697242512578487 41715418576045863768867731)
        ·
          refine ⟨62573127864068795653301597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41715418576045863768867731 62573127864068795653301597)
          ·
            refine ⟨23464922949025798369988099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62573127864068795653301597 23464922949025798369988099)
            ·
              refine ⟨35197384423538697554982149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23464922949025798369988099 35197384423538697554982149)
              ·
                refine ⟨6599509579413505791559153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35197384423538697554982149 6599509579413505791559153)
                ·
                  refine ⟨4949632184560129343669365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6599509579413505791559153 4949632184560129343669365)
                  ·
                    refine ⟨464028017302512125969003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4949632184560129343669365 464028017302512125969003)
                    ·
                      rfl

theorem cell22_1355537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_1355537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355537 prefixEnd_1355537 := by exact prefixLift 1355537
  have htrace : WordTrace (prefixWord ++ tailWord_1355537) baseStart_1355537 baseEnd_1355537 := by
    simpa [prefixWord, tailWord_1355537, baseEnd_1355537] using wordTrace_append hprefix tailTrace_1355537
  have hstable : (prefixWord ++ tailWord_1355537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355537).length < 2 ^ (prefixWord ++ tailWord_1355537).sum := by decide
  have hdescent : baseEnd_1355537 < baseStart_1355537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355543 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 1, 3]
def baseStart_1355543 : Nat := 118140960795 + 1355543 * 2 ^ 59
def prefixEnd_1355543 : Nat := 4983230072969 + 3 ^ 40 * 1355543 * 2
def baseEnd_1355543 : Nat := 464030071225130110318985

theorem tailTrace_1355543 : CollatzResearch.WordTrace tailWord_1355543 prefixEnd_1355543 464030071225130110318985 := by
  unfold tailWord_1355543
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440714928106694158191283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32960476618737796105460855 49440714928106694158191283)
  ·
    refine ⟨74161072392160041237286925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49440714928106694158191283 74161072392160041237286925)
    ·
      refine ⟨27810402147060015463982597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74161072392160041237286925 27810402147060015463982597)
      ·
        refine ⟨5214450402573752899496737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27810402147060015463982597 5214450402573752899496737)
        ·
          refine ⟨3910837801930314674622553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5214450402573752899496737 3910837801930314674622553)
          ·
            refine ⟨2933128351447736005966915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910837801930314674622553 2933128351447736005966915)
            ·
              refine ⟨4399692527171604008950373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933128351447736005966915 4399692527171604008950373)
              ·
                refine ⟨824942348844675751678195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4399692527171604008950373 824942348844675751678195)
                ·
                  refine ⟨1237413523267013627517293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824942348844675751678195 1237413523267013627517293)
                  ·
                    refine ⟨464030071225130110318985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237413523267013627517293 464030071225130110318985)
                    ·
                      rfl

theorem cell22_1355543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_1355543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355543 prefixEnd_1355543 := by exact prefixLift 1355543
  have htrace : WordTrace (prefixWord ++ tailWord_1355543) baseStart_1355543 baseEnd_1355543 := by
    simpa [prefixWord, tailWord_1355543, baseEnd_1355543] using wordTrace_append hprefix tailTrace_1355543
  have hstable : (prefixWord ++ tailWord_1355543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355543).length < 2 ^ (prefixWord ++ tailWord_1355543).sum := by decide
  have hdescent : baseEnd_1355543 < baseStart_1355543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355554 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1355554 : Nat := 118140960795 + 1355554 * 2 ^ 59
def prefixEnd_1355554 : Nat := 4983230072969 + 3 ^ 40 * 1355554 * 2
def baseEnd_1355554 : Nat := 464033836749929748293951

theorem tailTrace_1355554 : CollatzResearch.WordTrace tailWord_1355554 prefixEnd_1355554 464033836749929748293951 := by
  unfold tailWord_1355554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360279032766710759210429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32960744087377895357894477 12360279032766710759210429)
  ·
    refine ⟨4635104637287516534703911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12360279032766710759210429 4635104637287516534703911)
    ·
      refine ⟨6952656955931274802055867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4635104637287516534703911 6952656955931274802055867)
      ·
        refine ⟨10428985433896912203083801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952656955931274802055867 10428985433896912203083801)
        ·
          refine ⟨7821739075422684152312851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10428985433896912203083801 7821739075422684152312851)
          ·
            refine ⟨11732608613134026228469277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821739075422684152312851 11732608613134026228469277)
            ·
              refine ⟨4399728229925259835675979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11732608613134026228469277 4399728229925259835675979)
              ·
                refine ⟨6599592344887889753513969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399728229925259835675979 6599592344887889753513969)
                ·
                  refine ⟨4949694258665917315135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6599592344887889753513969 4949694258665917315135477)
                  ·
                    refine ⟨464033836749929748293951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4949694258665917315135477 464033836749929748293951)
                    ·
                      rfl

theorem cell22_1355554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1355554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355554 prefixEnd_1355554 := by exact prefixLift 1355554
  have htrace : WordTrace (prefixWord ++ tailWord_1355554) baseStart_1355554 baseEnd_1355554 := by
    simpa [prefixWord, tailWord_1355554, baseEnd_1355554] using wordTrace_append hprefix tailTrace_1355554
  have hstable : (prefixWord ++ tailWord_1355554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355554).length < 2 ^ (prefixWord ++ tailWord_1355554).sum := by decide
  have hdescent : baseEnd_1355554 < baseStart_1355554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355567 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 6]
def baseStart_1355567 : Nat := 118140960795 + 1355567 * 2 ^ 59
def prefixEnd_1355567 : Nat := 4983230072969 + 3 ^ 40 * 1355567 * 2
def baseEnd_1355567 : Nat := 154679428971867349239637

theorem tailTrace_1355567 : CollatzResearch.WordTrace tailWord_1355567 prefixEnd_1355567 154679428971867349239637 := by
  unfold tailWord_1355567
  simp only [CollatzResearch.WordTrace]
  refine ⟨49441590280019746257064955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32961060186679830838043303 49441590280019746257064955)
  ·
    refine ⟨74162385420029619385597433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49441590280019746257064955 74162385420029619385597433)
    ·
      refine ⟨55621789065022214539198075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74162385420029619385597433 55621789065022214539198075)
      ·
        refine ⟨83432683597533321808797113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55621789065022214539198075 83432683597533321808797113)
        ·
          refine ⟨62574512698149991356597835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83432683597533321808797113 62574512698149991356597835)
          ·
            refine ⟨93861769047224987034896753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62574512698149991356597835 93861769047224987034896753)
            ·
              refine ⟨70396326785418740276172565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93861769047224987034896753 70396326785418740276172565)
              ·
                refine ⟨3299827818066503450445589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70396326785418740276172565 3299827818066503450445589)
                ·
                  refine ⟨154679428971867349239637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3299827818066503450445589 154679428971867349239637)
                  ·
                    rfl

theorem cell22_1355567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_1355567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355567 prefixEnd_1355567 := by exact prefixLift 1355567
  have htrace : WordTrace (prefixWord ++ tailWord_1355567) baseStart_1355567 baseEnd_1355567 := by
    simpa [prefixWord, tailWord_1355567, baseEnd_1355567] using wordTrace_append hprefix tailTrace_1355567
  have hstable : (prefixWord ++ tailWord_1355567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355567).length < 2 ^ (prefixWord ++ tailWord_1355567).sum := by decide
  have hdescent : baseEnd_1355567 < baseStart_1355567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355569 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_1355569 : Nat := 118140960795 + 1355569 * 2 ^ 59
def prefixEnd_1355569 : Nat := 4983230072969 + 3 ^ 40 * 1355569 * 2
def baseEnd_1355569 : Nat := 464038971556474709168905

theorem tailTrace_1355569 : CollatzResearch.WordTrace tailWord_1355569 prefixEnd_1355569 464038971556474709168905 := by
  unfold tailWord_1355569
  simp only [CollatzResearch.WordTrace]
  refine ⟨49441663226012500598637761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32961108817341667065758507 49441663226012500598637761)
  ·
    refine ⟨37081247419509375448978321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49441663226012500598637761 37081247419509375448978321)
    ·
      refine ⟨27810935564632031586733741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37081247419509375448978321 27810935564632031586733741)
      ·
        refine ⟨10429100836737011845025153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27810935564632031586733741 10429100836737011845025153)
        ·
          refine ⟨7821825627552758883768865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10429100836737011845025153 7821825627552758883768865)
          ·
            refine ⟨5866369220664569162826649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7821825627552758883768865 5866369220664569162826649)
            ·
              refine ⟨4399776915498426872119987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866369220664569162826649 4399776915498426872119987)
              ·
                refine ⟨6599665373247640308179981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399776915498426872119987 6599665373247640308179981)
                ·
                  refine ⟨2474874514967865115567493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6599665373247640308179981 2474874514967865115567493)
                  ·
                    refine ⟨464038971556474709168905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2474874514967865115567493 464038971556474709168905)
                    ·
                      rfl

theorem cell22_1355569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_1355569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355569 prefixEnd_1355569 := by exact prefixLift 1355569
  have htrace : WordTrace (prefixWord ++ tailWord_1355569) baseStart_1355569 baseEnd_1355569 := by
    simpa [prefixWord, tailWord_1355569, baseEnd_1355569] using wordTrace_append hprefix tailTrace_1355569
  have hstable : (prefixWord ++ tailWord_1355569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355569).length < 2 ^ (prefixWord ++ tailWord_1355569).sum := by decide
  have hdescent : baseEnd_1355569 < baseStart_1355569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355590 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1355590 : Nat := 118140960795 + 1355590 * 2 ^ 59
def prefixEnd_1355590 : Nat := 4983230072969 + 3 ^ 40 * 1355590 * 2
def baseEnd_1355590 : Nat := 154682053428545884797947

theorem tailTrace_1355590 : CollatzResearch.WordTrace tailWord_1355590 prefixEnd_1355590 154682053428545884797947 := by
  unfold tailWord_1355590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545075911216763162036007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32961619439290947456768149 1545075911216763162036007)
  ·
    refine ⟨2317613866825144743054011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545075911216763162036007 2317613866825144743054011)
    ·
      refine ⟨3476420800237717114581017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317613866825144743054011 3476420800237717114581017)
      ·
        refine ⟨2607315600178287835935763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3476420800237717114581017 2607315600178287835935763)
        ·
          refine ⟨3910973400267431753903645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607315600178287835935763 3910973400267431753903645)
          ·
            refine ⟨1466615025100286907713867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3910973400267431753903645 1466615025100286907713867)
            ·
              refine ⟨2199922537650430361570801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466615025100286907713867 2199922537650430361570801)
              ·
                refine ⟨1649941903237822771178101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2199922537650430361570801 1649941903237822771178101)
                ·
                  refine ⟨154682053428545884797947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649941903237822771178101 154682053428545884797947)
                  ·
                    rfl

theorem cell22_1355590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1355590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355590 prefixEnd_1355590 := by exact prefixLift 1355590
  have htrace : WordTrace (prefixWord ++ tailWord_1355590) baseStart_1355590 baseEnd_1355590 := by
    simpa [prefixWord, tailWord_1355590, baseEnd_1355590] using wordTrace_append hprefix tailTrace_1355590
  have hstable : (prefixWord ++ tailWord_1355590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355590).length < 2 ^ (prefixWord ++ tailWord_1355590).sum := by decide
  have hdescent : baseEnd_1355590 < baseStart_1355590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355601 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 4]
def baseStart_1355601 : Nat := 118140960795 + 1355601 * 2 ^ 59
def prefixEnd_1355601 : Nat := 4983230072969 + 3 ^ 40 * 1355601 * 2
def baseEnd_1355601 : Nat := 154683308603479097456269

theorem tailTrace_1355601 : CollatzResearch.WordTrace tailWord_1355601 prefixEnd_1355601 154683308603479097456269 := by
  unfold tailWord_1355601
  simp only [CollatzResearch.WordTrace]
  refine ⟨49442830361896570063802657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32961886907931046709201771 49442830361896570063802657)
  ·
    refine ⟨37082122771422427547851993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49442830361896570063802657 37082122771422427547851993)
    ·
      refine ⟨27811592078566820660888995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37082122771422427547851993 27811592078566820660888995)
      ·
        refine ⟨41717388117850230991333493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27811592078566820660888995 41717388117850230991333493)
        ·
          refine ⟨3911005136048459155437515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41717388117850230991333493 3911005136048459155437515)
          ·
            refine ⟨5866507704072688733156273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911005136048459155437515 5866507704072688733156273)
            ·
              refine ⟨4399880778054516549867205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866507704072688733156273 4399880778054516549867205)
              ·
                refine ⟨824977645885221853100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4399880778054516549867205 824977645885221853100101)
                ·
                  refine ⟨154683308603479097456269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824977645885221853100101 154683308603479097456269)
                  ·
                    rfl

theorem cell22_1355601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_1355601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355601 prefixEnd_1355601 := by exact prefixLift 1355601
  have htrace : WordTrace (prefixWord ++ tailWord_1355601) baseStart_1355601 baseEnd_1355601 := by
    simpa [prefixWord, tailWord_1355601, baseEnd_1355601] using wordTrace_append hprefix tailTrace_1355601
  have hstable : (prefixWord ++ tailWord_1355601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355601).length < 2 ^ (prefixWord ++ tailWord_1355601).sum := by decide
  have hdescent : baseEnd_1355601 < baseStart_1355601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355616 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_1355616 : Nat := 118140960795 + 1355616 * 2 ^ 59
def prefixEnd_1355616 : Nat := 4983230072969 + 3 ^ 40 * 1355616 * 2
def baseEnd_1355616 : Nat := 464055060616982253243761

theorem tailTrace_1355616 : CollatzResearch.WordTrace tailWord_1355616 prefixEnd_1355616 464055060616982253243761 := by
  unfold tailWord_1355616
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721688728421113812799351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32962251637894818417065801 24721688728421113812799351)
  ·
    refine ⟨37082533092631670719199027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24721688728421113812799351 37082533092631670719199027)
    ·
      refine ⟨55623799638947506078798541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37082533092631670719199027 55623799638947506078798541)
      ·
        refine ⟨20858924864605314779549453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55623799638947506078798541 20858924864605314779549453)
        ·
          refine ⟨7822096824226993042331045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20858924864605314779549453 7822096824226993042331045)
          ·
            refine ⟨1466643154542561195437071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7822096824226993042331045 1466643154542561195437071)
            ·
              refine ⟨2199964731813841793155607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466643154542561195437071 2199964731813841793155607)
              ·
                refine ⟨3299947097720762689733411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199964731813841793155607 3299947097720762689733411)
                ·
                  refine ⟨4949920646581144034600117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299947097720762689733411 4949920646581144034600117)
                  ·
                    refine ⟨464055060616982253243761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4949920646581144034600117 464055060616982253243761)
                    ·
                      rfl

theorem cell22_1355616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_1355616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355616 prefixEnd_1355616 := by exact prefixLift 1355616
  have htrace : WordTrace (prefixWord ++ tailWord_1355616) baseStart_1355616 baseEnd_1355616 := by
    simpa [prefixWord, tailWord_1355616, baseEnd_1355616] using wordTrace_append hprefix tailTrace_1355616
  have hstable : (prefixWord ++ tailWord_1355616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355616).length < 2 ^ (prefixWord ++ tailWord_1355616).sum := by decide
  have hdescent : baseEnd_1355616 < baseStart_1355616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355627 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_1355627 : Nat := 118140960795 + 1355627 * 2 ^ 59
def prefixEnd_1355627 : Nat := 4983230072969 + 3 ^ 40 * 1355627 * 2
def baseEnd_1355627 : Nat := 464058826141781891218727

theorem tailTrace_1355627 : CollatzResearch.WordTrace tailWord_1355627 prefixEnd_1355627 464058826141781891218727 := by
  unfold tailWord_1355627
  simp only [CollatzResearch.WordTrace]
  refine ⟨49443778659802376504249135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32962519106534917669499423 49443778659802376504249135)
  ·
    refine ⟨74165667989703564756373703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49443778659802376504249135 74165667989703564756373703)
    ·
      refine ⟨111248501984555347134560555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74165667989703564756373703 111248501984555347134560555)
      ·
        refine ⟨166872752976833020701840833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111248501984555347134560555 166872752976833020701840833)
        ·
          refine ⟨125154564732624765526380625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166872752976833020701840833 125154564732624765526380625)
          ·
            refine ⟨93865923549468574144785469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125154564732624765526380625 93865923549468574144785469)
            ·
              refine ⟨35199721331050715304294551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93865923549468574144785469 35199721331050715304294551)
              ·
                refine ⟨52799581996576072956441827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35199721331050715304294551 52799581996576072956441827)
                ·
                  refine ⟨79199372994864109434662741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52799581996576072956441827 79199372994864109434662741)
                  ·
                    refine ⟨464058826141781891218727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79199372994864109434662741 464058826141781891218727)
                    ·
                      rfl

theorem cell22_1355627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_1355627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355627 prefixEnd_1355627 := by exact prefixLift 1355627
  have htrace : WordTrace (prefixWord ++ tailWord_1355627) baseStart_1355627 baseEnd_1355627 := by
    simpa [prefixWord, tailWord_1355627, baseEnd_1355627] using wordTrace_append hprefix tailTrace_1355627
  have hstable : (prefixWord ++ tailWord_1355627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355627).length < 2 ^ (prefixWord ++ tailWord_1355627).sum := by decide
  have hdescent : baseEnd_1355627 < baseStart_1355627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355646 : List Nat := [4, 2, 3, 1, 1, 1, 10]
def baseStart_1355646 : Nat := 118140960795 + 1355646 * 2 ^ 59
def prefixEnd_1355646 : Nat := 4983230072969 + 3 ^ 40 * 1355646 * 2
def baseEnd_1355646 : Nat := 17187604823336006481247

theorem tailTrace_1355646 : CollatzResearch.WordTrace tailWord_1355646 prefixEnd_1355646 17187604823336006481247 := by
  unfold tailWord_1355646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6180558955841692843648849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32962981097822361832793861 6180558955841692843648849)
  ·
    refine ⟨4635419216881269632736637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6180558955841692843648849 4635419216881269632736637)
    ·
      refine ⟨1738282206330476112276239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4635419216881269632736637 1738282206330476112276239)
      ·
        refine ⟨2607423309495714168414359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738282206330476112276239 2607423309495714168414359)
        ·
          refine ⟨3911134964243571252621539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607423309495714168414359 3911134964243571252621539)
          ·
            refine ⟨5866702446365356878932309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911134964243571252621539 5866702446365356878932309)
            ·
              refine ⟨17187604823336006481247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5866702446365356878932309 17187604823336006481247)
              ·
                rfl

theorem cell22_1355646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 10].length) (baseStart_1355646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355646 prefixEnd_1355646 := by exact prefixLift 1355646
  have htrace : WordTrace (prefixWord ++ tailWord_1355646) baseStart_1355646 baseEnd_1355646 := by
    simpa [prefixWord, tailWord_1355646, baseEnd_1355646] using wordTrace_append hprefix tailTrace_1355646
  have hstable : (prefixWord ++ tailWord_1355646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355646).length < 2 ^ (prefixWord ++ tailWord_1355646).sum := by decide
  have hdescent : baseEnd_1355646 < baseStart_1355646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355719 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 6]
def baseStart_1355719 : Nat := 118140960795 + 1355719 * 2 ^ 59
def prefixEnd_1355719 : Nat := 4983230072969 + 3 ^ 40 * 1355719 * 2
def baseEnd_1355719 : Nat := 154696773207308105972815

theorem tailTrace_1355719 : CollatzResearch.WordTrace tailWord_1355719 prefixEnd_1355719 154696773207308105972815 := by
  unfold tailWord_1355719
  simp only [CollatzResearch.WordTrace]
  refine ⟨49447134175469076216598211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32964756116979384144398807 49447134175469076216598211)
  ·
    refine ⟨74170701263203614324897317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49447134175469076216598211 74170701263203614324897317)
    ·
      refine ⟨13907006486850677685918247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74170701263203614324897317 13907006486850677685918247)
      ·
        refine ⟨20860509730276016528877371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13907006486850677685918247 20860509730276016528877371)
        ·
          refine ⟨31290764595414024793316057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20860509730276016528877371 31290764595414024793316057)
          ·
            refine ⟨23468073446560518594987043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31290764595414024793316057 23468073446560518594987043)
            ·
              refine ⟨35202110169840777892480565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23468073446560518594987043 35202110169840777892480565)
              ·
                refine ⟨3300197828422572927420053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35202110169840777892480565 3300197828422572927420053)
                ·
                  refine ⟨154696773207308105972815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3300197828422572927420053 154696773207308105972815)
                  ·
                    rfl

theorem cell22_1355719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_1355719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355719 prefixEnd_1355719 := by exact prefixLift 1355719
  have htrace : WordTrace (prefixWord ++ tailWord_1355719) baseStart_1355719 baseEnd_1355719 := by
    simpa [prefixWord, tailWord_1355719, baseEnd_1355719] using wordTrace_append hprefix tailTrace_1355719
  have hstable : (prefixWord ++ tailWord_1355719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355719).length < 2 ^ (prefixWord ++ tailWord_1355719).sum := by decide
  have hdescent : baseEnd_1355719 < baseStart_1355719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355768 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1355768 : Nat := 118140960795 + 1355768 * 2 ^ 59
def prefixEnd_1355768 : Nat := 4983230072969 + 3 ^ 40 * 1355768 * 2
def baseEnd_1355768 : Nat := 464107093323304523443295

theorem tailTrace_1355768 : CollatzResearch.WordTrace tailWord_1355768 prefixEnd_1355768 464107093323304523443295 := by
  unfold tailWord_1355768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24724460676145778792565979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32965947568194371723421305 24724460676145778792565979)
  ·
    refine ⟨37086691014218668188848969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24724460676145778792565979 37086691014218668188848969)
    ·
      refine ⟨27815018260664001141636727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37086691014218668188848969 27815018260664001141636727)
      ·
        refine ⟨41722527390996001712455091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27815018260664001141636727 41722527390996001712455091)
        ·
          refine ⟨62583791086494002568682637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41722527390996001712455091 62583791086494002568682637)
          ·
            refine ⟨23468921657435250963255989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62583791086494002568682637 23468921657435250963255989)
            ·
              refine ⟨2200211405384554777805249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23468921657435250963255989 2200211405384554777805249)
              ·
                refine ⟨1650158554038416083353937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200211405384554777805249 1650158554038416083353937)
                ·
                  refine ⟨1237618915528812062515453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650158554038416083353937 1237618915528812062515453)
                  ·
                    refine ⟨464107093323304523443295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237618915528812062515453 464107093323304523443295)
                    ·
                      rfl

theorem cell22_1355768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1355768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355768 prefixEnd_1355768 := by exact prefixLift 1355768
  have htrace : WordTrace (prefixWord ++ tailWord_1355768) baseStart_1355768 baseEnd_1355768 := by
    simpa [prefixWord, tailWord_1355768, baseEnd_1355768] using wordTrace_append hprefix tailTrace_1355768
  have hstable : (prefixWord ++ tailWord_1355768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355768).length < 2 ^ (prefixWord ++ tailWord_1355768).sum := by decide
  have hdescent : baseEnd_1355768 < baseStart_1355768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355789 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1355789 : Nat := 118140960795 + 1355789 * 2 ^ 59
def prefixEnd_1355789 : Nat := 4983230072969 + 3 ^ 40 * 1355789 * 2
def baseEnd_1355789 : Nat := 464114282052467468668231

theorem tailTrace_1355789 : CollatzResearch.WordTrace tailWord_1355789 prefixEnd_1355789 464114282052467468668231 := by
  unfold tailWord_1355789
  simp only [CollatzResearch.WordTrace]
  refine ⟨49449687285215478171646421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32966458190143652114430947 49449687285215478171646421)
  ·
    refine ⟨1158977045747237769647963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49449687285215478171646421 1158977045747237769647963)
    ·
      refine ⟨1738465568620856654471945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158977045747237769647963 1738465568620856654471945)
      ·
        refine ⟨1303849176465642490853959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738465568620856654471945 1303849176465642490853959)
        ·
          refine ⟨1955773764698463736280939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303849176465642490853959 1955773764698463736280939)
          ·
            refine ⟨2933660647047695604421409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955773764698463736280939 2933660647047695604421409)
            ·
              refine ⟨2200245485285771703316057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933660647047695604421409 2200245485285771703316057)
              ·
                refine ⟨1650184113964328777487043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200245485285771703316057 1650184113964328777487043)
                ·
                  refine ⟨2475276170946493166230565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650184113964328777487043 2475276170946493166230565)
                  ·
                    refine ⟨464114282052467468668231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2475276170946493166230565 464114282052467468668231)
                    ·
                      rfl

theorem cell22_1355789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1355789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355789 prefixEnd_1355789 := by exact prefixLift 1355789
  have htrace : WordTrace (prefixWord ++ tailWord_1355789) baseStart_1355789 baseEnd_1355789 := by
    simpa [prefixWord, tailWord_1355789, baseEnd_1355789] using wordTrace_append hprefix tailTrace_1355789
  have hstable : (prefixWord ++ tailWord_1355789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355789).length < 2 ^ (prefixWord ++ tailWord_1355789).sum := by decide
  have hdescent : baseEnd_1355789 < baseStart_1355789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355815 : List Nat := [1, 1, 7, 1, 3, 1, 8]
def baseStart_1355815 : Nat := 118140960795 + 1355815 * 2 ^ 59
def prefixEnd_1355815 : Nat := 4983230072969 + 3 ^ 40 * 1355815 * 2
def baseEnd_1355815 : Nat := 17189747495696743241413

theorem tailTrace_1355815 : CollatzResearch.WordTrace tailWord_1355815 prefixEnd_1355815 17189747495696743241413 := by
  unfold tailWord_1355815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49450635583121284612092899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32967090388747523074728599 49450635583121284612092899)
  ·
    refine ⟨74175953374681926918139349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49450635583121284612092899 74175953374681926918139349)
    ·
      refine ⟨1738498907219107662143891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74175953374681926918139349 1738498907219107662143891)
      ·
        refine ⟨2607748360828661493215837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738498907219107662143891 2607748360828661493215837)
        ·
          refine ⟨977905635310748059955939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2607748360828661493215837 977905635310748059955939)
          ·
            refine ⟨1466858452966122089933909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977905635310748059955939 1466858452966122089933909)
            ·
              refine ⟨17189747495696743241413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1466858452966122089933909 17189747495696743241413)
              ·
                rfl

theorem cell22_1355815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 8].length) (baseStart_1355815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355815 prefixEnd_1355815 := by exact prefixLift 1355815
  have htrace : WordTrace (prefixWord ++ tailWord_1355815) baseStart_1355815 baseEnd_1355815 := by
    simpa [prefixWord, tailWord_1355815, baseEnd_1355815] using wordTrace_append hprefix tailTrace_1355815
  have hstable : (prefixWord ++ tailWord_1355815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355815).length < 2 ^ (prefixWord ++ tailWord_1355815).sum := by decide
  have hdescent : baseEnd_1355815 < baseStart_1355815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355826 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1355826 : Nat := 118140960795 + 1355826 * 2 ^ 59
def prefixEnd_1355826 : Nat := 4983230072969 + 3 ^ 40 * 1355826 * 2
def baseEnd_1355826 : Nat := 154708982636203901831039

theorem tailTrace_1355826 : CollatzResearch.WordTrace tailWord_1355826 prefixEnd_1355826 154708982636203901831039 := by
  unfold tailWord_1355826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362759196520358372685833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32967357857387622327162221 12362759196520358372685833)
  ·
    refine ⟨9272069397390268779514375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12362759196520358372685833 9272069397390268779514375)
    ·
      refine ⟨13908104096085403169271563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272069397390268779514375 13908104096085403169271563)
      ·
        refine ⟨20862156144128104753907345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13908104096085403169271563 20862156144128104753907345)
        ·
          refine ⟨15646617108096078565430509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20862156144128104753907345 15646617108096078565430509)
          ·
            refine ⟨5867481415536029462036441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15646617108096078565430509 5867481415536029462036441)
            ·
              refine ⟨4400611061652022096527331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5867481415536029462036441 4400611061652022096527331)
              ·
                refine ⟨6600916592478033144790997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400611061652022096527331 6600916592478033144790997)
                ·
                  refine ⟨154708982636203901831039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6600916592478033144790997 154708982636203901831039)
                  ·
                    rfl

theorem cell22_1355826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1355826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355826 prefixEnd_1355826 := by exact prefixLift 1355826
  have htrace : WordTrace (prefixWord ++ tailWord_1355826) baseStart_1355826 baseEnd_1355826 := by
    simpa [prefixWord, tailWord_1355826, baseEnd_1355826] using wordTrace_append hprefix tailTrace_1355826
  have hstable : (prefixWord ++ tailWord_1355826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355826).length < 2 ^ (prefixWord ++ tailWord_1355826).sum := by decide
  have hdescent : baseEnd_1355826 < baseStart_1355826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355937 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1355937 : Nat := 118140960795 + 1355937 * 2 ^ 59
def prefixEnd_1355937 : Nat := 4983230072969 + 3 ^ 40 * 1355937 * 2
def baseEnd_1355937 : Nat := 464164945477044415967777

theorem tailTrace_1355937 : CollatzResearch.WordTrace tailWord_1355937 prefixEnd_1355937 464164945477044415967777 := by
  unfold tailWord_1355937
  simp only [CollatzResearch.WordTrace]
  refine ⟨49455085288679299448034065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32970056859119532965356043 49455085288679299448034065)
  ·
    refine ⟨37091313966509474586025549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49455085288679299448034065 37091313966509474586025549)
    ·
      refine ⟨13909242737441052969759581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37091313966509474586025549 13909242737441052969759581)
      ·
        refine ⟨5215966026540394863659843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13909242737441052969759581 5215966026540394863659843)
        ·
          refine ⟨7823949039810592295489765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215966026540394863659843 7823949039810592295489765)
          ·
            refine ⟨1466990444964486055404331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7823949039810592295489765 1466990444964486055404331)
            ·
              refine ⟨2200485667446729083106497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466990444964486055404331 2200485667446729083106497)
              ·
                refine ⟨1650364250585046812329873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200485667446729083106497 1650364250585046812329873)
                ·
                  refine ⟨1237773187938785109247405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650364250585046812329873 1237773187938785109247405)
                  ·
                    refine ⟨464164945477044415967777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237773187938785109247405 464164945477044415967777)
                    ·
                      rfl

theorem cell22_1355937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1355937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1355937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1355937 prefixEnd_1355937 := by exact prefixLift 1355937
  have htrace : WordTrace (prefixWord ++ tailWord_1355937) baseStart_1355937 baseEnd_1355937 := by
    simpa [prefixWord, tailWord_1355937, baseEnd_1355937] using wordTrace_append hprefix tailTrace_1355937
  have hstable : (prefixWord ++ tailWord_1355937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355937).length < 2 ^ (prefixWord ++ tailWord_1355937).sum := by decide
  have hdescent : baseEnd_1355937 < baseStart_1355937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356072 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1356072 : Nat := 118140960795 + 1356072 * 2 ^ 59
def prefixEnd_1356072 : Nat := 4983230072969 + 3 ^ 40 * 1356072 * 2
def baseEnd_1356072 : Nat := 464211158735949063842363

theorem tailTrace_1356072 : CollatzResearch.WordTrace tailWord_1356072 prefixEnd_1356072 464211158735949063842363 := by
  unfold tailWord_1356072
  simp only [CollatzResearch.WordTrace]
  refine ⟨24730004571595108752099235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32973339428793478336132313 24730004571595108752099235)
  ·
    refine ⟨37095006857392663128148853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24730004571595108752099235 37095006857392663128148853)
    ·
      refine ⟨3477656892880562168263955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37095006857392663128148853 3477656892880562168263955)
      ·
        refine ⟨5216485339320843252395933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477656892880562168263955 5216485339320843252395933)
        ·
          refine ⟨1956182002245316219648475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5216485339320843252395933 1956182002245316219648475)
          ·
            refine ⟨2934273003367974329472713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956182002245316219648475 2934273003367974329472713)
            ·
              refine ⟨2200704752525980747104535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934273003367974329472713 2200704752525980747104535)
              ·
                refine ⟨3301057128788971120656803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200704752525980747104535 3301057128788971120656803)
                ·
                  refine ⟨4951585693183456680985205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301057128788971120656803 4951585693183456680985205)
                  ·
                    refine ⟨464211158735949063842363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4951585693183456680985205 464211158735949063842363)
                    ·
                      rfl

theorem cell22_1356072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1356072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356072 prefixEnd_1356072 := by exact prefixLift 1356072
  have htrace : WordTrace (prefixWord ++ tailWord_1356072) baseStart_1356072 baseEnd_1356072 := by
    simpa [prefixWord, tailWord_1356072, baseEnd_1356072] using wordTrace_append hprefix tailTrace_1356072
  have hstable : (prefixWord ++ tailWord_1356072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356072).length < 2 ^ (prefixWord ++ tailWord_1356072).sum := by decide
  have hdescent : baseEnd_1356072 < baseStart_1356072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356085 : List Nat := [1, 3, 3, 1, 2, 1, 5, 6]
def baseStart_1356085 : Nat := 118140960795 + 1356085 * 2 ^ 59
def prefixEnd_1356085 : Nat := 4983230072969 + 3 ^ 40 * 1356085 * 2
def baseEnd_1356085 : Nat := 51579512100180151474147

theorem tailTrace_1356085 : CollatzResearch.WordTrace tailWord_1356085 prefixEnd_1356085 51579512100180151474147 := by
  unfold tailWord_1356085
  simp only [CollatzResearch.WordTrace]
  refine ⟨49460483292143120724421709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32973655528095413816281139 49460483292143120724421709)
  ·
    refine ⟨18547681234553670271658141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49460483292143120724421709 18547681234553670271658141)
    ·
      refine ⟨6955380462957626351871803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18547681234553670271658141 6955380462957626351871803)
      ·
        refine ⟨10433070694436439527807705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955380462957626351871803 10433070694436439527807705)
        ·
          refine ⟨7824803020827329645855779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10433070694436439527807705 7824803020827329645855779)
          ·
            refine ⟨11737204531240994468783669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7824803020827329645855779 11737204531240994468783669)
            ·
              refine ⟨1100362924803843231448469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11737204531240994468783669 1100362924803843231448469)
              ·
                refine ⟨51579512100180151474147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1100362924803843231448469 51579512100180151474147)
                ·
                  rfl

theorem cell22_1356085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 6].length) (baseStart_1356085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356085 prefixEnd_1356085 := by exact prefixLift 1356085
  have htrace : WordTrace (prefixWord ++ tailWord_1356085) baseStart_1356085 baseEnd_1356085 := by
    simpa [prefixWord, tailWord_1356085, baseEnd_1356085] using wordTrace_append hprefix tailTrace_1356085
  have hstable : (prefixWord ++ tailWord_1356085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356085).length < 2 ^ (prefixWord ++ tailWord_1356085).sum := by decide
  have hdescent : baseEnd_1356085 < baseStart_1356085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356220 : List Nat := [2, 2, 2, 4, 1, 11]
def baseStart_1356220 : Nat := 118140960795 + 1356220 * 2 ^ 59
def prefixEnd_1356220 : Nat := 4983230072969 + 3 ^ 40 * 1356220 * 2
def baseEnd_1356220 : Nat := 5731627434080568038789

theorem tailTrace_1356220 : CollatzResearch.WordTrace tailWord_1356220 prefixEnd_1356220 5731627434080568038789 := by
  unfold tailWord_1356220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732703573327019390293057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32976938097769359187057409 24732703573327019390293057)
  ·
    refine ⟨18549527679995264542719793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24732703573327019390293057 18549527679995264542719793)
    ·
      refine ⟨13912145759996448407039845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18549527679995264542719793 13912145759996448407039845)
      ·
        refine ⟨2608527329999334076319971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13912145759996448407039845 2608527329999334076319971)
        ·
          refine ⟨3912790994999001114479957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608527329999334076319971 3912790994999001114479957)
          ·
            refine ⟨5731627434080568038789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3912790994999001114479957 5731627434080568038789)
            ·
              rfl

theorem cell22_1356220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 11].length) (baseStart_1356220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356220 prefixEnd_1356220 := by exact prefixLift 1356220
  have htrace : WordTrace (prefixWord ++ tailWord_1356220) baseStart_1356220 baseEnd_1356220 := by
    simpa [prefixWord, tailWord_1356220, baseEnd_1356220] using wordTrace_append hprefix tailTrace_1356220
  have hstable : (prefixWord ++ tailWord_1356220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356220).length < 2 ^ (prefixWord ++ tailWord_1356220).sum := by decide
  have hdescent : baseEnd_1356220 < baseStart_1356220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356222 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1356222 : Nat := 118140960795 + 1356222 * 2 ^ 59
def prefixEnd_1356222 : Nat := 4983230072969 + 3 ^ 40 * 1356222 * 2
def baseEnd_1356222 : Nat := 464262506801398672591903

theorem tailTrace_1356222 : CollatzResearch.WordTrace tailWord_1356222 prefixEnd_1356222 464262506801398672591903 := by
  unfold tailWord_1356222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183185011580849140269865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32976986728431195414772613 6183185011580849140269865)
  ·
    refine ⟨4637388758685636855202399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6183185011580849140269865 4637388758685636855202399)
    ·
      refine ⟨6956083138028455282803599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637388758685636855202399 6956083138028455282803599)
      ·
        refine ⟨10434124707042682924205399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956083138028455282803599 10434124707042682924205399)
        ·
          refine ⟨15651187060564024386308099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10434124707042682924205399 15651187060564024386308099)
          ·
            refine ⟨23476780590846036579462149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15651187060564024386308099 23476780590846036579462149)
            ·
              refine ⟨4401896360783631858649153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23476780590846036579462149 4401896360783631858649153)
              ·
                refine ⟨3301422270587723893986865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401896360783631858649153 3301422270587723893986865)
                ·
                  refine ⟨2476066702940792920490149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301422270587723893986865 2476066702940792920490149)
                  ·
                    refine ⟨464262506801398672591903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476066702940792920490149 464262506801398672591903)
                    ·
                      rfl

theorem cell22_1356222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1356222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356222 prefixEnd_1356222 := by exact prefixLift 1356222
  have htrace : WordTrace (prefixWord ++ tailWord_1356222) baseStart_1356222 baseEnd_1356222 := by
    simpa [prefixWord, tailWord_1356222, baseEnd_1356222] using wordTrace_append hprefix tailTrace_1356222
  have hstable : (prefixWord ++ tailWord_1356222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356222).length < 2 ^ (prefixWord ++ tailWord_1356222).sum := by decide
  have hdescent : baseEnd_1356222 < baseStart_1356222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356250 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1356250 : Nat := 118140960795 + 1356250 * 2 ^ 59
def prefixEnd_1356250 : Nat := 4983230072969 + 3 ^ 40 * 1356250 * 2
def baseEnd_1356250 : Nat := 464272091773615932891817

theorem tailTrace_1356250 : CollatzResearch.WordTrace tailWord_1356250 prefixEnd_1356250 464272091773615932891817 := by
  unfold tailWord_1356250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12366625334136338476044551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32977667557696902602785469 12366625334136338476044551)
  ·
    refine ⟨18549938001204507714066827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12366625334136338476044551 18549938001204507714066827)
    ·
      refine ⟨27824907001806761571100241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18549938001204507714066827 27824907001806761571100241)
      ·
        refine ⟨20868680251355071178325181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27824907001806761571100241 20868680251355071178325181)
        ·
          refine ⟨7825755094258151691871943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20868680251355071178325181 7825755094258151691871943)
          ·
            refine ⟨11738632641387227537807915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825755094258151691871943 11738632641387227537807915)
            ·
              refine ⟨17607948962080841306711873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738632641387227537807915 17607948962080841306711873)
              ·
                refine ⟨13205961721560630980033905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17607948962080841306711873 13205961721560630980033905)
                ·
                  refine ⟨9904471291170473235025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13205961721560630980033905 9904471291170473235025429)
                  ·
                    refine ⟨464272091773615932891817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9904471291170473235025429 464272091773615932891817)
                    ·
                      rfl

theorem cell22_1356250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1356250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356250 prefixEnd_1356250 := by exact prefixLift 1356250
  have htrace : WordTrace (prefixWord ++ tailWord_1356250) baseStart_1356250 baseEnd_1356250 := by
    simpa [prefixWord, tailWord_1356250, baseEnd_1356250] using wordTrace_append hprefix tailTrace_1356250
  have hstable : (prefixWord ++ tailWord_1356250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356250).length < 2 ^ (prefixWord ++ tailWord_1356250).sum := by decide
  have hdescent : baseEnd_1356250 < baseStart_1356250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356280 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1356280 : Nat := 118140960795 + 1356280 * 2 ^ 59
def prefixEnd_1356280 : Nat := 4983230072969 + 3 ^ 40 * 1356280 * 2
def baseEnd_1356280 : Nat := 464282361386705854641725

theorem tailTrace_1356280 : CollatzResearch.WordTrace tailWord_1356280 prefixEnd_1356280 464282361386705854641725 := by
  unfold tailWord_1356280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733797763218334513885147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32978397017624446018513529 24733797763218334513885147)
  ·
    refine ⟨37100696644827501770827721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24733797763218334513885147 37100696644827501770827721)
    ·
      refine ⟨27825522483620626328120791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37100696644827501770827721 27825522483620626328120791)
      ·
        refine ⟨41738283725430939492181187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27825522483620626328120791 41738283725430939492181187)
        ·
          refine ⟨62607425588146409238271781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41738283725430939492181187 62607425588146409238271781)
          ·
            refine ⟨11738892297777451732175959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62607425588146409238271781 11738892297777451732175959)
            ·
              refine ⟨17608338446666177598263939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738892297777451732175959 17608338446666177598263939)
              ·
                refine ⟨26412507669999266397395909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17608338446666177598263939 26412507669999266397395909)
                ·
                  refine ⟨4952345188124862449511733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26412507669999266397395909 4952345188124862449511733)
                  ·
                    refine ⟨464282361386705854641725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4952345188124862449511733 464282361386705854641725)
                    ·
                      rfl

theorem cell22_1356280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1356280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356280 prefixEnd_1356280 := by exact prefixLift 1356280
  have htrace : WordTrace (prefixWord ++ tailWord_1356280) baseStart_1356280 baseEnd_1356280 := by
    simpa [prefixWord, tailWord_1356280, baseEnd_1356280] using wordTrace_append hprefix tailTrace_1356280
  have hstable : (prefixWord ++ tailWord_1356280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356280).length < 2 ^ (prefixWord ++ tailWord_1356280).sum := by decide
  have hdescent : baseEnd_1356280 < baseStart_1356280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356299 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 5]
def baseStart_1356299 : Nat := 118140960795 + 1356299 * 2 ^ 59
def prefixEnd_1356299 : Nat := 4983230072969 + 3 ^ 40 * 1356299 * 2
def baseEnd_1356299 : Nat := 154762955158332046138889

theorem tailTrace_1356299 : CollatzResearch.WordTrace tailWord_1356299 prefixEnd_1356299 154762955158332046138889 := by
  unfold tailWord_1356299
  simp only [CollatzResearch.WordTrace]
  refine ⟨49468288513367835272711951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32978859008911890181807967 49468288513367835272711951)
  ·
    refine ⟨74202432770051752909067927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49468288513367835272711951 74202432770051752909067927)
    ·
      refine ⟨111303649155077629363601891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74202432770051752909067927 111303649155077629363601891)
      ·
        refine ⟨166955473732616444045402837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111303649155077629363601891 166955473732616444045402837)
        ·
          refine ⟨3913018915608197907314129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166955473732616444045402837 3913018915608197907314129)
          ·
            refine ⟨2934764186706148430485597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913018915608197907314129 2934764186706148430485597)
            ·
              refine ⟨1100536570014805661432099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2934764186706148430485597 1100536570014805661432099)
              ·
                refine ⟨1650804855022208492148149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100536570014805661432099 1650804855022208492148149)
                ·
                  refine ⟨154762955158332046138889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650804855022208492148149 154762955158332046138889)
                  ·
                    rfl

theorem cell22_1356299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 5].length) (baseStart_1356299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356299 prefixEnd_1356299 := by exact prefixLift 1356299
  have htrace : WordTrace (prefixWord ++ tailWord_1356299) baseStart_1356299 baseEnd_1356299 := by
    simpa [prefixWord, tailWord_1356299, baseEnd_1356299] using wordTrace_append hprefix tailTrace_1356299
  have hstable : (prefixWord ++ tailWord_1356299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356299).length < 2 ^ (prefixWord ++ tailWord_1356299).sum := by decide
  have hdescent : baseEnd_1356299 < baseStart_1356299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356320 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_1356320 : Nat := 118140960795 + 1356320 * 2 ^ 59
def prefixEnd_1356320 : Nat := 4983230072969 + 3 ^ 40 * 1356320 * 2
def baseEnd_1356320 : Nat := 464296054204159083641603

theorem tailTrace_1356320 : CollatzResearch.WordTrace tailWord_1356320 prefixEnd_1356320 464296054204159083641603 := by
  unfold tailWord_1356320
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734527223145877929613207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32979369630861170572817609 24734527223145877929613207)
  ·
    refine ⟨37101790834718816894419811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24734527223145877929613207 37101790834718816894419811)
    ·
      refine ⟨55652686252078225341629717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37101790834718816894419811 55652686252078225341629717)
      ·
        refine ⟨2608719668066166812888893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55652686252078225341629717 2608719668066166812888893)
        ·
          refine ⟨978269875524812554833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2608719668066166812888893 978269875524812554833335)
          ·
            refine ⟨1467404813287218832250003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978269875524812554833335 1467404813287218832250003)
            ·
              refine ⟨2201107219930828248375005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467404813287218832250003 2201107219930828248375005)
              ·
                refine ⟨825415207474060593140627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201107219930828248375005 825415207474060593140627)
                ·
                  refine ⟨1238122811211090889710941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825415207474060593140627 1238122811211090889710941)
                  ·
                    refine ⟨464296054204159083641603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238122811211090889710941 464296054204159083641603)
                    ·
                      rfl

theorem cell22_1356320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_1356320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356320 prefixEnd_1356320 := by exact prefixLift 1356320
  have htrace : WordTrace (prefixWord ++ tailWord_1356320) baseStart_1356320 baseEnd_1356320 := by
    simpa [prefixWord, tailWord_1356320, baseEnd_1356320] using wordTrace_append hprefix tailTrace_1356320
  have hstable : (prefixWord ++ tailWord_1356320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356320).length < 2 ^ (prefixWord ++ tailWord_1356320).sum := by decide
  have hdescent : baseEnd_1356320 < baseStart_1356320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356350 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1356350 : Nat := 118140960795 + 1356350 * 2 ^ 59
def prefixEnd_1356350 : Nat := 4983230072969 + 3 ^ 40 * 1356350 * 2
def baseEnd_1356350 : Nat := 154768774605749668463837

theorem tailTrace_1356350 : CollatzResearch.WordTrace tailWord_1356350 prefixEnd_1356350 154768774605749668463837 := by
  unfold tailWord_1356350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183768579522883872852313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32980099090788713988545669 6183768579522883872852313)
  ·
    refine ⟨4637826434642162904639235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6183768579522883872852313 4637826434642162904639235)
    ·
      refine ⟨6956739651963244356958853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637826434642162904639235 6956739651963244356958853)
      ·
        refine ⟨1304388684743108316929785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6956739651963244356958853 1304388684743108316929785)
        ·
          refine ⟨978291513557331237697339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304388684743108316929785 978291513557331237697339)
          ·
            refine ⟨1467437270335996856546009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978291513557331237697339 1467437270335996856546009)
            ·
              refine ⟨1100577952751997642409507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467437270335996856546009 1100577952751997642409507)
              ·
                refine ⟨1650866929127996463614261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100577952751997642409507 1650866929127996463614261)
                ·
                  refine ⟨154768774605749668463837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1650866929127996463614261 154768774605749668463837)
                  ·
                    rfl

theorem cell22_1356350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1356350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356350 prefixEnd_1356350 := by exact prefixLift 1356350
  have htrace : WordTrace (prefixWord ++ tailWord_1356350) baseStart_1356350 baseEnd_1356350 := by
    simpa [prefixWord, tailWord_1356350, baseEnd_1356350] using wordTrace_append hprefix tailTrace_1356350
  have hstable : (prefixWord ++ tailWord_1356350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356350).length < 2 ^ (prefixWord ++ tailWord_1356350).sum := by decide
  have hdescent : baseEnd_1356350 < baseStart_1356350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356372 : List Nat := [2, 4, 1, 1, 1, 3, 2, 8]
def baseStart_1356372 : Nat := 118140960795 + 1356372 * 2 ^ 59
def prefixEnd_1356372 : Nat := 4983230072969 + 3 ^ 40 * 1356372 * 2
def baseEnd_1356372 : Nat := 51590428318538697926827

theorem tailTrace_1356372 : CollatzResearch.WordTrace tailWord_1356372 prefixEnd_1356372 51590428318538697926827 := by
  unfold tailWord_1356372
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735475521051684370059685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32980634028068912493412913 24735475521051684370059685)
  ·
    refine ⟨4637901660197190819386191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24735475521051684370059685 4637901660197190819386191)
    ·
      refine ⟨6956852490295786229079287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637901660197190819386191 6956852490295786229079287)
      ·
        refine ⟨10435278735443679343618931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956852490295786229079287 10435278735443679343618931)
        ·
          refine ⟨15652918103165519015428397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435278735443679343618931 15652918103165519015428397)
          ·
            refine ⟨5869844288687069630785649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15652918103165519015428397 5869844288687069630785649)
            ·
              refine ⟨4402383216515302223089237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869844288687069630785649 4402383216515302223089237)
              ·
                refine ⟨51590428318538697926827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4402383216515302223089237 51590428318538697926827)
                ·
                  rfl

theorem cell22_1356372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_1356372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356372 prefixEnd_1356372 := by exact prefixLift 1356372
  have htrace : WordTrace (prefixWord ++ tailWord_1356372) baseStart_1356372 baseEnd_1356372 := by
    simpa [prefixWord, tailWord_1356372, baseEnd_1356372] using wordTrace_append hprefix tailTrace_1356372
  have hstable : (prefixWord ++ tailWord_1356372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356372).length < 2 ^ (prefixWord ++ tailWord_1356372).sum := by decide
  have hdescent : baseEnd_1356372 < baseStart_1356372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356406 : List Nat := [5, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1356406 : Nat := 118140960795 + 1356406 * 2 ^ 59
def prefixEnd_1356406 : Nat := 4983230072969 + 3 ^ 40 * 1356406 * 2
def baseEnd_1356406 : Nat := 51591721529075947332371

theorem tailTrace_1356406 : CollatzResearch.WordTrace tailWord_1356406 prefixEnd_1356406 51591721529075947332371 := by
  unfold tailWord_1356406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092011945248762034178567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32981460749320128364571381 3092011945248762034178567)
  ·
    refine ⟨4638017917873143051267851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092011945248762034178567 4638017917873143051267851)
    ·
      refine ⟨6957026876809714576901777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638017917873143051267851 6957026876809714576901777)
      ·
        refine ⟨5217770157607285932676333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6957026876809714576901777 5217770157607285932676333)
        ·
          refine ⟨1956663809102732224753625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5217770157607285932676333 1956663809102732224753625)
          ·
            refine ⟨1467497856827049168565219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956663809102732224753625 1467497856827049168565219)
            ·
              refine ⟨2201246785240573752847829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467497856827049168565219 2201246785240573752847829)
              ·
                refine ⟨51591721529075947332371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2201246785240573752847829 51591721529075947332371)
                ·
                  rfl

theorem cell22_1356406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1356406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356406 prefixEnd_1356406 := by exact prefixLift 1356406
  have htrace : WordTrace (prefixWord ++ tailWord_1356406) baseStart_1356406 baseEnd_1356406 := by
    simpa [prefixWord, tailWord_1356406, baseEnd_1356406] using wordTrace_append hprefix tailTrace_1356406
  have hstable : (prefixWord ++ tailWord_1356406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356406).length < 2 ^ (prefixWord ++ tailWord_1356406).sum := by decide
  have hdescent : baseEnd_1356406 < baseStart_1356406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356513 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 4]
def baseStart_1356513 : Nat := 118140960795 + 1356513 * 2 ^ 59
def prefixEnd_1356513 : Nat := 4983230072969 + 3 ^ 40 * 1356513 * 2
def baseEnd_1356513 : Nat := 154787374016123637855337

theorem tailTrace_1356513 : CollatzResearch.WordTrace tailWord_1356513 prefixEnd_1356513 154787374016123637855337 := by
  unfold tailWord_1356513
  simp only [CollatzResearch.WordTrace]
  refine ⟨49476093734592549821002193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32984062489728366547334795 49476093734592549821002193)
  ·
    refine ⟨37107070300944412365751645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49476093734592549821002193 37107070300944412365751645)
    ·
      refine ⟨13915151362854154637156867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37107070300944412365751645 13915151362854154637156867)
      ·
        refine ⟨20872727044281231955735301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13915151362854154637156867 20872727044281231955735301)
        ·
          refine ⟨3913636320802730991700369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20872727044281231955735301 3913636320802730991700369)
          ·
            refine ⟨2935227240602048243775277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913636320802730991700369 2935227240602048243775277)
            ·
              refine ⟨1100710215225768091415729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935227240602048243775277 1100710215225768091415729)
              ·
                refine ⟨825532661419326068561797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100710215225768091415729 825532661419326068561797)
                ·
                  refine ⟨154787374016123637855337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825532661419326068561797 154787374016123637855337)
                  ·
                    rfl

theorem cell22_1356513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_1356513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356513 prefixEnd_1356513 := by exact prefixLift 1356513
  have htrace : WordTrace (prefixWord ++ tailWord_1356513) baseStart_1356513 baseEnd_1356513 := by
    simpa [prefixWord, tailWord_1356513, baseEnd_1356513] using wordTrace_append hprefix tailTrace_1356513
  have hstable : (prefixWord ++ tailWord_1356513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356513).length < 2 ^ (prefixWord ++ tailWord_1356513).sum := by decide
  have hdescent : baseEnd_1356513 < baseStart_1356513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356532 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1356532 : Nat := 118140960795 + 1356532 * 2 ^ 59
def prefixEnd_1356532 : Nat := 4983230072969 + 3 ^ 40 * 1356532 * 2
def baseEnd_1356532 : Nat := 464368626136661197340953

theorem tailTrace_1356532 : CollatzResearch.WordTrace tailWord_1356532 prefixEnd_1356532 464368626136661197340953 := by
  unfold tailWord_1356532
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738393360761858032971925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32984524481015810710629233 24738393360761858032971925)
  ·
    refine ⟨1159612188785712095295559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24738393360761858032971925 1159612188785712095295559)
    ·
      refine ⟨1739418283178568142943339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1159612188785712095295559 1739418283178568142943339)
      ·
        refine ⟨2609127424767852214415009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739418283178568142943339 2609127424767852214415009)
        ·
          refine ⟨1956845568575889160811257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2609127424767852214415009 1956845568575889160811257)
          ·
            refine ⟨1467634176431916870608443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956845568575889160811257 1467634176431916870608443)
            ·
              refine ⟨2201451264647875305912665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467634176431916870608443 2201451264647875305912665)
              ·
                refine ⟨1651088448485906479434499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201451264647875305912665 1651088448485906479434499)
                ·
                  refine ⟨2476632672728859719151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651088448485906479434499 2476632672728859719151749)
                  ·
                    refine ⟨464368626136661197340953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476632672728859719151749 464368626136661197340953)
                    ·
                      rfl

theorem cell22_1356532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1356532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356532 prefixEnd_1356532 := by exact prefixLift 1356532
  have htrace : WordTrace (prefixWord ++ tailWord_1356532) baseStart_1356532 baseEnd_1356532 := by
    simpa [prefixWord, tailWord_1356532, baseEnd_1356532] using wordTrace_append hprefix tailTrace_1356532
  have hstable : (prefixWord ++ tailWord_1356532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356532).length < 2 ^ (prefixWord ++ tailWord_1356532).sum := by decide
  have hdescent : baseEnd_1356532 < baseStart_1356532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356599 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1356599 : Nat := 118140960795 + 1356599 * 2 ^ 59
def prefixEnd_1356599 : Nat := 4983230072969 + 3 ^ 40 * 1356599 * 2
def baseEnd_1356599 : Nat := 464391561605895355915747

theorem tailTrace_1356599 : CollatzResearch.WordTrace tailWord_1356599 prefixEnd_1356599 464391561605895355915747 := by
  unfold tailWord_1356599
  simp only [CollatzResearch.WordTrace]
  refine ⟨49479230412280986508632851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32986153608187324339088567 49479230412280986508632851)
  ·
    refine ⟨74218845618421479762949277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49479230412280986508632851 74218845618421479762949277)
    ·
      refine ⟨27832067106908054911105979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74218845618421479762949277 27832067106908054911105979)
      ·
        refine ⟨41748100660362082366658969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27832067106908054911105979 41748100660362082366658969)
        ·
          refine ⟨31311075495271561774994227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41748100660362082366658969 31311075495271561774994227)
          ·
            refine ⟨46966613242907342662491341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31311075495271561774994227 46966613242907342662491341)
            ·
              refine ⟨17612479966090253498434253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46966613242907342662491341 17612479966090253498434253)
              ·
                refine ⟨6604679987283845061912845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17612479966090253498434253 6604679987283845061912845)
                ·
                  refine ⟨2476754995231441898217317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6604679987283845061912845 2476754995231441898217317)
                  ·
                    refine ⟨464391561605895355915747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476754995231441898217317 464391561605895355915747)
                    ·
                      rfl

theorem cell22_1356599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1356599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356599 prefixEnd_1356599 := by exact prefixLift 1356599
  have htrace : WordTrace (prefixWord ++ tailWord_1356599) baseStart_1356599 baseEnd_1356599 := by
    simpa [prefixWord, tailWord_1356599, baseEnd_1356599] using wordTrace_append hprefix tailTrace_1356599
  have hstable : (prefixWord ++ tailWord_1356599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356599).length < 2 ^ (prefixWord ++ tailWord_1356599).sum := by decide
  have hdescent : baseEnd_1356599 < baseStart_1356599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356616 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1356616 : Nat := 118140960795 + 1356616 * 2 ^ 59
def prefixEnd_1356616 : Nat := 4983230072969 + 3 ^ 40 * 1356616 * 2
def baseEnd_1356616 : Nat := 464397381053312978240695

theorem tailTrace_1356616 : CollatzResearch.WordTrace tailWord_1356616 prefixEnd_1356616 464397381053312978240695 := by
  unfold tailWord_1356616
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739925226609699206000851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32986566968812932274667801 24739925226609699206000851)
  ·
    refine ⟨37109887839914548809001277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24739925226609699206000851 37109887839914548809001277)
    ·
      refine ⟨13916207939967955803375479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37109887839914548809001277 13916207939967955803375479)
      ·
        refine ⟨20874311909951933705063219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13916207939967955803375479 20874311909951933705063219)
        ·
          refine ⟨31311467864927900557594829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20874311909951933705063219 31311467864927900557594829)
          ·
            refine ⟨11741800449347962709098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31311467864927900557594829 11741800449347962709098061)
            ·
              refine ⟨4403175168505486015911773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11741800449347962709098061 4403175168505486015911773)
              ·
                refine ⟨1651190688189557255966915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4403175168505486015911773 1651190688189557255966915)
                ·
                  refine ⟨2476786032284335883950373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651190688189557255966915 2476786032284335883950373)
                  ·
                    refine ⟨464397381053312978240695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2476786032284335883950373 464397381053312978240695)
                    ·
                      rfl

theorem cell22_1356616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1356616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356616 prefixEnd_1356616 := by exact prefixLift 1356616
  have htrace : WordTrace (prefixWord ++ tailWord_1356616) baseStart_1356616 baseEnd_1356616 := by
    simpa [prefixWord, tailWord_1356616, baseEnd_1356616] using wordTrace_append hprefix tailTrace_1356616
  have hstable : (prefixWord ++ tailWord_1356616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356616).length < 2 ^ (prefixWord ++ tailWord_1356616).sum := by decide
  have hdescent : baseEnd_1356616 < baseStart_1356616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356631 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 6]
def baseStart_1356631 : Nat := 118140960795 + 1356631 * 2 ^ 59
def prefixEnd_1356631 : Nat := 4983230072969 + 3 ^ 40 * 1356631 * 2
def baseEnd_1356631 : Nat := 154800838619952646371883

theorem tailTrace_1356631 : CollatzResearch.WordTrace tailWord_1356631 prefixEnd_1356631 154800838619952646371883 := by
  unfold tailWord_1356631
  simp only [CollatzResearch.WordTrace]
  refine ⟨49480397548165055973797747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32986931698776703982531831 49480397548165055973797747)
  ·
    refine ⟨74220596322247583960696621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49480397548165055973797747 74220596322247583960696621)
    ·
      refine ⟨27832723620842843985261233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74220596322247583960696621 27832723620842843985261233)
      ·
        refine ⟨20874542715632132988945925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27832723620842843985261233 20874542715632132988945925)
        ·
          refine ⟨3913976759181024935427361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20874542715632132988945925 3913976759181024935427361)
          ·
            refine ⟨2935482569385768701570521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913976759181024935427361 2935482569385768701570521)
            ·
              refine ⟨2201611927039326526177891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935482569385768701570521 2201611927039326526177891)
              ·
                refine ⟨3302417890558989789266837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201611927039326526177891 3302417890558989789266837)
                ·
                  refine ⟨154800838619952646371883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3302417890558989789266837 154800838619952646371883)
                  ·
                    rfl

theorem cell22_1356631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_1356631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356631 prefixEnd_1356631 := by exact prefixLift 1356631
  have htrace : WordTrace (prefixWord ++ tailWord_1356631) baseStart_1356631 baseEnd_1356631 := by
    simpa [prefixWord, tailWord_1356631, baseEnd_1356631] using wordTrace_append hprefix tailTrace_1356631
  have hstable : (prefixWord ++ tailWord_1356631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356631).length < 2 ^ (prefixWord ++ tailWord_1356631).sum := by decide
  have hdescent : baseEnd_1356631 < baseStart_1356631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356661 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1356661 : Nat := 118140960795 + 1356661 * 2 ^ 59
def prefixEnd_1356661 : Nat := 4983230072969 + 3 ^ 40 * 1356661 * 2
def baseEnd_1356661 : Nat := 464412785472947860865557

theorem tailTrace_1356661 : CollatzResearch.WordTrace tailWord_1356661 prefixEnd_1356661 464412785472947860865557 := by
  unfold tailWord_1356661
  simp only [CollatzResearch.WordTrace]
  refine ⟨49481491738056371097389837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32987661158704247398259891 49481491738056371097389837)
  ·
    refine ⟨18555559401771139161521189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49481491738056371097389837 18555559401771139161521189)
    ·
      refine ⟨3479167387832088592785223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18555559401771139161521189 3479167387832088592785223)
      ·
        refine ⟨5218751081748132889177835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479167387832088592785223 5218751081748132889177835)
        ·
          refine ⟨7828126622622199333766753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218751081748132889177835 7828126622622199333766753)
          ·
            refine ⟨5871094966966649500325065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7828126622622199333766753 5871094966966649500325065)
            ·
              refine ⟨4403321225224987125243799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871094966966649500325065 4403321225224987125243799)
              ·
                refine ⟨6604981837837480687865699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403321225224987125243799 6604981837837480687865699)
                ·
                  refine ⟨9907472756756221031798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6604981837837480687865699 9907472756756221031798549)
                  ·
                    refine ⟨464412785472947860865557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9907472756756221031798549 464412785472947860865557)
                    ·
                      rfl

theorem cell22_1356661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1356661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356661 prefixEnd_1356661 := by exact prefixLift 1356661
  have htrace : WordTrace (prefixWord ++ tailWord_1356661) baseStart_1356661 baseEnd_1356661 := by
    simpa [prefixWord, tailWord_1356661, baseEnd_1356661] using wordTrace_append hprefix tailTrace_1356661
  have hstable : (prefixWord ++ tailWord_1356661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356661).length < 2 ^ (prefixWord ++ tailWord_1356661).sum := by decide
  have hdescent : baseEnd_1356661 < baseStart_1356661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356689 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_1356689 : Nat := 118140960795 + 1356689 * 2 ^ 59
def prefixEnd_1356689 : Nat := 4983230072969 + 3 ^ 40 * 1356689 * 2
def baseEnd_1356689 : Nat := 464422370445165121165471

theorem tailTrace_1356689 : CollatzResearch.WordTrace tailWord_1356689 prefixEnd_1356689 464422370445165121165471 := by
  unfold tailWord_1356689
  simp only [CollatzResearch.WordTrace]
  refine ⟨49482512981954931879409121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32988341987969954586272747 49482512981954931879409121)
  ·
    refine ⟨37111884736466198909556841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49482512981954931879409121 37111884736466198909556841)
    ·
      refine ⟨27833913552349649182167631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37111884736466198909556841 27833913552349649182167631)
      ·
        refine ⟨41750870328524473773251447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27833913552349649182167631 41750870328524473773251447)
        ·
          refine ⟨62626305492786710659877171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41750870328524473773251447 62626305492786710659877171)
          ·
            refine ⟨93939458239180065989815757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62626305492786710659877171 93939458239180065989815757)
            ·
              refine ⟨35227296839692524746180909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93939458239180065989815757 35227296839692524746180909)
              ·
                refine ⟨13210236314884696779817841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35227296839692524746180909 13210236314884696779817841)
                ·
                  refine ⟨9907677236163522584863381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13210236314884696779817841 9907677236163522584863381)
                  ·
                    refine ⟨464422370445165121165471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9907677236163522584863381 464422370445165121165471)
                    ·
                      rfl

theorem cell22_1356689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_1356689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356689 prefixEnd_1356689 := by exact prefixLift 1356689
  have htrace : WordTrace (prefixWord ++ tailWord_1356689) baseStart_1356689 baseEnd_1356689 := by
    simpa [prefixWord, tailWord_1356689, baseEnd_1356689] using wordTrace_append hprefix tailTrace_1356689
  have hstable : (prefixWord ++ tailWord_1356689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356689).length < 2 ^ (prefixWord ++ tailWord_1356689).sum := by decide
  have hdescent : baseEnd_1356689 < baseStart_1356689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356691 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 3, 3]
def baseStart_1356691 : Nat := 118140960795 + 1356691 * 2 ^ 59
def prefixEnd_1356691 : Nat := 4983230072969 + 3 ^ 40 * 1356691 * 2
def baseEnd_1356691 : Nat := 464423055086037782615465

theorem tailTrace_1356691 : CollatzResearch.WordTrace tailWord_1356691 prefixEnd_1356691 464423055086037782615465 := by
  unfold tailWord_1356691
  simp only [CollatzResearch.WordTrace]
  refine ⟨49482585927947686220981927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32988390618631790813987951 49482585927947686220981927)
  ·
    refine ⟨74223878891921529331472891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49482585927947686220981927 74223878891921529331472891)
    ·
      refine ⟨111335818337882293997209337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74223878891921529331472891 111335818337882293997209337)
      ·
        refine ⟨83501863753411720497907003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111335818337882293997209337 83501863753411720497907003)
        ·
          refine ⟨125252795630117580746860505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83501863753411720497907003 125252795630117580746860505)
          ·
            refine ⟨93939596722588185560145379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125252795630117580746860505 93939596722588185560145379)
            ·
              refine ⟨140909395083882278340218069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93939596722588185560145379 140909395083882278340218069)
              ·
                refine ⟨3302563947278490898598861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140909395083882278340218069 3302563947278490898598861)
                ·
                  refine ⟨1238461480229434086974573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3302563947278490898598861 1238461480229434086974573)
                  ·
                    refine ⟨464423055086037782615465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238461480229434086974573 464423055086037782615465)
                    ·
                      rfl

theorem cell22_1356691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].length) (baseStart_1356691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356691 prefixEnd_1356691 := by exact prefixLift 1356691
  have htrace : WordTrace (prefixWord ++ tailWord_1356691) baseStart_1356691 baseEnd_1356691 := by
    simpa [prefixWord, tailWord_1356691, baseEnd_1356691] using wordTrace_append hprefix tailTrace_1356691
  have hstable : (prefixWord ++ tailWord_1356691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356691).length < 2 ^ (prefixWord ++ tailWord_1356691).sum := by decide
  have hdescent : baseEnd_1356691 < baseStart_1356691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356719 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1356719 : Nat := 118140960795 + 1356719 * 2 ^ 59
def prefixEnd_1356719 : Nat := 4983230072969 + 3 ^ 40 * 1356719 * 2
def baseEnd_1356719 : Nat := 464432640058255042915379

theorem tailTrace_1356719 : CollatzResearch.WordTrace tailWord_1356719 prefixEnd_1356719 464432640058255042915379 := by
  unfold tailWord_1356719
  simp only [CollatzResearch.WordTrace]
  refine ⟨49483607171846247003001211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32989071447897498002000807 49483607171846247003001211)
  ·
    refine ⟨74225410757769370504501817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49483607171846247003001211 74225410757769370504501817)
    ·
      refine ⟨55669058068327027878376363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74225410757769370504501817 55669058068327027878376363)
      ·
        refine ⟨83503587102490541817564545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55669058068327027878376363 83503587102490541817564545)
        ·
          refine ⟨62627690326867906363173409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83503587102490541817564545 62627690326867906363173409)
          ·
            refine ⟨46970767745150929772380057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62627690326867906363173409 46970767745150929772380057)
            ·
              refine ⟨35228075808863197329285043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46970767745150929772380057 35228075808863197329285043)
              ·
                refine ⟨52842113713294795993927565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35228075808863197329285043 52842113713294795993927565)
                ·
                  refine ⟨19815792642485548497722837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52842113713294795993927565 19815792642485548497722837)
                  ·
                    refine ⟨464432640058255042915379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19815792642485548497722837 464432640058255042915379)
                    ·
                      rfl

theorem cell22_1356719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1356719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356719 prefixEnd_1356719 := by exact prefixLift 1356719
  have htrace : WordTrace (prefixWord ++ tailWord_1356719) baseStart_1356719 baseEnd_1356719 := by
    simpa [prefixWord, tailWord_1356719, baseEnd_1356719] using wordTrace_append hprefix tailTrace_1356719
  have hstable : (prefixWord ++ tailWord_1356719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356719).length < 2 ^ (prefixWord ++ tailWord_1356719).sum := by decide
  have hdescent : baseEnd_1356719 < baseStart_1356719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356725 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1356725 : Nat := 118140960795 + 1356725 * 2 ^ 59
def prefixEnd_1356725 : Nat := 4983230072969 + 3 ^ 40 * 1356725 * 2
def baseEnd_1356725 : Nat := 464434693980873027265361

theorem tailTrace_1356725 : CollatzResearch.WordTrace tailWord_1356725 prefixEnd_1356725 464434693980873027265361 := by
  unfold tailWord_1356725
  simp only [CollatzResearch.WordTrace]
  refine ⟨49483826009824510027719629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32989217339883006685146419 49483826009824510027719629)
  ·
    refine ⟨18556434753684191260394861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49483826009824510027719629 18556434753684191260394861)
    ·
      refine ⟨6958663032631571722648073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18556434753684191260394861 6958663032631571722648073)
      ·
        refine ⟨5218997274473678791986055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6958663032631571722648073 5218997274473678791986055)
        ·
          refine ⟨7828495911710518187979083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218997274473678791986055 7828495911710518187979083)
          ·
            refine ⟨11742743867565777281968625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828495911710518187979083 11742743867565777281968625)
            ·
              refine ⟨8807057900674332961476469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11742743867565777281968625 8807057900674332961476469)
              ·
                refine ⟨825661678188218715138419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8807057900674332961476469 825661678188218715138419)
                ·
                  refine ⟨1238492517282328072707629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825661678188218715138419 1238492517282328072707629)
                  ·
                    refine ⟨464434693980873027265361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238492517282328072707629 464434693980873027265361)
                    ·
                      rfl

theorem cell22_1356725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1356725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356725 prefixEnd_1356725 := by exact prefixLift 1356725
  have htrace : WordTrace (prefixWord ++ tailWord_1356725) baseStart_1356725 baseEnd_1356725 := by
    simpa [prefixWord, tailWord_1356725, baseEnd_1356725] using wordTrace_append hprefix tailTrace_1356725
  have hstable : (prefixWord ++ tailWord_1356725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356725).length < 2 ^ (prefixWord ++ tailWord_1356725).sum := by decide
  have hdescent : baseEnd_1356725 < baseStart_1356725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356751 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_1356751 : Nat := 118140960795 + 1356751 * 2 ^ 59
def prefixEnd_1356751 : Nat := 4983230072969 + 3 ^ 40 * 1356751 * 2
def baseEnd_1356751 : Nat := 464443594312217626115281

theorem tailTrace_1356751 : CollatzResearch.WordTrace tailWord_1356751 prefixEnd_1356751 464443594312217626115281 := by
  unfold tailWord_1356751
  simp only [CollatzResearch.WordTrace]
  refine ⟨49484774307730316468166107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32989849538486877645444071 49484774307730316468166107)
  ·
    refine ⟨74227161461595474702249161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49484774307730316468166107 74227161461595474702249161)
    ·
      refine ⟨55670371096196606026686871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74227161461595474702249161 55670371096196606026686871)
      ·
        refine ⟨83505556644294909040030307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55670371096196606026686871 83505556644294909040030307)
        ·
          refine ⟨125258334966442363560045461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83505556644294909040030307 125258334966442363560045461)
          ·
            refine ⟨5871484451551985791877131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125258334966442363560045461 5871484451551985791877131)
            ·
              refine ⟨8807226677327978687815697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871484451551985791877131 8807226677327978687815697)
              ·
                refine ⟨6605420007995984015861773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8807226677327978687815697 6605420007995984015861773)
                ·
                  refine ⟨2477032502998494005948165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6605420007995984015861773 2477032502998494005948165)
                  ·
                    refine ⟨464443594312217626115281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477032502998494005948165 464443594312217626115281)
                    ·
                      rfl

theorem cell22_1356751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_1356751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356751 prefixEnd_1356751 := by exact prefixLift 1356751
  have htrace : WordTrace (prefixWord ++ tailWord_1356751) baseStart_1356751 baseEnd_1356751 := by
    simpa [prefixWord, tailWord_1356751, baseEnd_1356751] using wordTrace_append hprefix tailTrace_1356751
  have hstable : (prefixWord ++ tailWord_1356751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356751).length < 2 ^ (prefixWord ++ tailWord_1356751).sum := by decide
  have hdescent : baseEnd_1356751 < baseStart_1356751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356783 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 4]
def baseStart_1356783 : Nat := 118140960795 + 1356783 * 2 ^ 59
def prefixEnd_1356783 : Nat := 4983230072969 + 3 ^ 40 * 1356783 * 2
def baseEnd_1356783 : Nat := 154818182855393403105061

theorem tailTrace_1356783 : CollatzResearch.WordTrace tailWord_1356783 prefixEnd_1356783 154818182855393403105061 := by
  unfold tailWord_1356783
  simp only [CollatzResearch.WordTrace]
  refine ⟨49485941443614385933331003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32990627629076257288887335 49485941443614385933331003)
  ·
    refine ⟨74228912165421578899996505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49485941443614385933331003 74228912165421578899996505)
    ·
      refine ⟨55671684124066184174997379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74228912165421578899996505 55671684124066184174997379)
      ·
        refine ⟨83507526186099276262496069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55671684124066184174997379 83507526186099276262496069)
        ·
          refine ⟨15657661159893614299218013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83507526186099276262496069 15657661159893614299218013)
          ·
            refine ⟨5871622934960105362206755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15657661159893614299218013 5871622934960105362206755)
            ·
              refine ⟨8807434402440158043310133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871622934960105362206755 8807434402440158043310133)
              ·
                refine ⟨825696975228764816560325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8807434402440158043310133 825696975228764816560325)
                ·
                  refine ⟨154818182855393403105061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825696975228764816560325 154818182855393403105061)
                  ·
                    rfl

theorem cell22_1356783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 4].length) (baseStart_1356783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356783 prefixEnd_1356783 := by exact prefixLift 1356783
  have htrace : WordTrace (prefixWord ++ tailWord_1356783) baseStart_1356783 baseEnd_1356783 := by
    simpa [prefixWord, tailWord_1356783, baseEnd_1356783] using wordTrace_append hprefix tailTrace_1356783
  have hstable : (prefixWord ++ tailWord_1356783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356783).length < 2 ^ (prefixWord ++ tailWord_1356783).sum := by decide
  have hdescent : baseEnd_1356783 < baseStart_1356783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356785 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_1356785 : Nat := 118140960795 + 1356785 * 2 ^ 59
def prefixEnd_1356785 : Nat := 4983230072969 + 3 ^ 40 * 1356785 * 2
def baseEnd_1356785 : Nat := 464455233207052870765177

theorem tailTrace_1356785 : CollatzResearch.WordTrace tailWord_1356785 prefixEnd_1356785 464455233207052870765177 := by
  unfold tailWord_1356785
  simp only [CollatzResearch.WordTrace]
  refine ⟨49486014389607140274903809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32990676259738093516602539 49486014389607140274903809)
  ·
    refine ⟨37114510792205355206177857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49486014389607140274903809 37114510792205355206177857)
    ·
      refine ⟨27835883094154016404633393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37114510792205355206177857 27835883094154016404633393)
      ·
        refine ⟨20876912320615512303475045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27835883094154016404633393 20876912320615512303475045)
        ·
          refine ⟨3914421060115408556901571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20876912320615512303475045 3914421060115408556901571)
          ·
            refine ⟨5871631590173112835352357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914421060115408556901571 5871631590173112835352357)
            ·
              refine ⟨1100930923157458656628567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5871631590173112835352357 1100930923157458656628567)
              ·
                refine ⟨1651396384736187984942851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100930923157458656628567 1651396384736187984942851)
                ·
                  refine ⟨2477094577104281977414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651396384736187984942851 2477094577104281977414277)
                  ·
                    refine ⟨464455233207052870765177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477094577104281977414277 464455233207052870765177)
                    ·
                      rfl

theorem cell22_1356785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_1356785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356785 prefixEnd_1356785 := by exact prefixLift 1356785
  have htrace : WordTrace (prefixWord ++ tailWord_1356785) baseStart_1356785 baseEnd_1356785 := by
    simpa [prefixWord, tailWord_1356785, baseEnd_1356785] using wordTrace_append hprefix tailTrace_1356785
  have hstable : (prefixWord ++ tailWord_1356785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356785).length < 2 ^ (prefixWord ++ tailWord_1356785).sum := by decide
  have hdescent : baseEnd_1356785 < baseStart_1356785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356789 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 5]
def baseStart_1356789 : Nat := 118140960795 + 1356789 * 2 ^ 59
def prefixEnd_1356789 : Nat := 4983230072969 + 3 ^ 40 * 1356789 * 2
def baseEnd_1356789 : Nat := 154818867496266064555055

theorem tailTrace_1356789 : CollatzResearch.WordTrace tailWord_1356789 prefixEnd_1356789 154818867496266064555055 := by
  unfold tailWord_1356789
  simp only [CollatzResearch.WordTrace]
  refine ⟨49486160281592648958049421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32990773521061765972032947 49486160281592648958049421)
  ·
    refine ⟨18557310105597243359268533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49486160281592648958049421 18557310105597243359268533)
    ·
      refine ⟨1739747822399741564931425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18557310105597243359268533 1739747822399741564931425)
      ·
        refine ⟨1304810866799806173698569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1739747822399741564931425 1304810866799806173698569)
        ·
          refine ⟨978608150099854630273927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304810866799806173698569 978608150099854630273927)
          ·
            refine ⟨1467912225149781945410891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978608150099854630273927 1467912225149781945410891)
            ·
              refine ⟨2201868337724672918116337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467912225149781945410891 2201868337724672918116337)
              ·
                refine ⟨1651401253293504688587253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201868337724672918116337 1651401253293504688587253)
                ·
                  refine ⟨154818867496266064555055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1651401253293504688587253 154818867496266064555055)
                  ·
                    rfl

theorem cell22_1356789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_1356789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356789 prefixEnd_1356789 := by exact prefixLift 1356789
  have htrace : WordTrace (prefixWord ++ tailWord_1356789) baseStart_1356789 baseEnd_1356789 := by
    simpa [prefixWord, tailWord_1356789, baseEnd_1356789] using wordTrace_append hprefix tailTrace_1356789
  have hstable : (prefixWord ++ tailWord_1356789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356789).length < 2 ^ (prefixWord ++ tailWord_1356789).sum := by decide
  have hdescent : baseEnd_1356789 < baseStart_1356789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356826 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1356826 : Nat := 118140960795 + 1356826 * 2 ^ 59
def prefixEnd_1356826 : Nat := 4983230072969 + 3 ^ 40 * 1356826 * 2
def baseEnd_1356826 : Nat := 464469268344942430490051

theorem tailTrace_1356826 : CollatzResearch.WordTrace tailWord_1356826 prefixEnd_1356826 464469268344942430490051 := by
  unfold tailWord_1356826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371877445614651069286583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32991673188305736184764221 12371877445614651069286583)
  ·
    refine ⟨18557816168421976603929875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371877445614651069286583 18557816168421976603929875)
    ·
      refine ⟨27836724252632964905894813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18557816168421976603929875 27836724252632964905894813)
      ·
        refine ⟨10438771594737361839710555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27836724252632964905894813 10438771594737361839710555)
        ·
          refine ⟨15658157392106042759565833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438771594737361839710555 15658157392106042759565833)
          ·
            refine ⟨11743618044079532069674375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15658157392106042759565833 11743618044079532069674375)
            ·
              refine ⟨17615427066119298104511563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11743618044079532069674375 17615427066119298104511563)
              ·
                refine ⟨26423140599178947156767345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17615427066119298104511563 26423140599178947156767345)
                ·
                  refine ⟨19817355449384210367575509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26423140599178947156767345 19817355449384210367575509)
                  ·
                    refine ⟨464469268344942430490051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19817355449384210367575509 464469268344942430490051)
                    ·
                      rfl

theorem cell22_1356826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1356826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356826 prefixEnd_1356826 := by exact prefixLift 1356826
  have htrace : WordTrace (prefixWord ++ tailWord_1356826) baseStart_1356826 baseEnd_1356826 := by
    simpa [prefixWord, tailWord_1356826, baseEnd_1356826] using wordTrace_append hprefix tailTrace_1356826
  have hstable : (prefixWord ++ tailWord_1356826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356826).length < 2 ^ (prefixWord ++ tailWord_1356826).sum := by decide
  have hdescent : baseEnd_1356826 < baseStart_1356826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356828 : List Nat := [2, 2, 3, 1, 4, 1, 1, 8]
def baseStart_1356828 : Nat := 118140960795 + 1356828 * 2 ^ 59
def prefixEnd_1356828 : Nat := 4983230072969 + 3 ^ 40 * 1356828 * 2
def baseEnd_1356828 : Nat := 51607772553979454660005

theorem tailTrace_1356828 : CollatzResearch.WordTrace tailWord_1356828 prefixEnd_1356828 51607772553979454660005 := by
  unfold tailWord_1356828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743791364225679309359569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32991721818967572412479425 24743791364225679309359569)
  ·
    refine ⟨18557843523169259482019677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24743791364225679309359569 18557843523169259482019677)
    ·
      refine ⟨6959191321188472305757379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18557843523169259482019677 6959191321188472305757379)
      ·
        refine ⟨10438786981782708458636069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959191321188472305757379 10438786981782708458636069)
        ·
          refine ⟨1957272559084257835994263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10438786981782708458636069 1957272559084257835994263)
          ·
            refine ⟨2935908838626386753991395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957272559084257835994263 2935908838626386753991395)
            ·
              refine ⟨4403863257939580130987093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935908838626386753991395 4403863257939580130987093)
              ·
                refine ⟨51607772553979454660005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4403863257939580130987093 51607772553979454660005)
                ·
                  rfl

theorem cell22_1356828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_1356828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356828 prefixEnd_1356828 := by exact prefixLift 1356828
  have htrace : WordTrace (prefixWord ++ tailWord_1356828) baseStart_1356828 baseEnd_1356828 := by
    simpa [prefixWord, tailWord_1356828, baseEnd_1356828] using wordTrace_append hprefix tailTrace_1356828
  have hstable : (prefixWord ++ tailWord_1356828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356828).length < 2 ^ (prefixWord ++ tailWord_1356828).sum := by decide
  have hdescent : baseEnd_1356828 < baseStart_1356828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356860 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1356860 : Nat := 118140960795 + 1356860 * 2 ^ 59
def prefixEnd_1356860 : Nat := 4983230072969 + 3 ^ 40 * 1356860 * 2
def baseEnd_1356860 : Nat := 464480907239777675139947

theorem tailTrace_1356860 : CollatzResearch.WordTrace tailWord_1356860 prefixEnd_1356860 464480907239777675139947 := by
  unfold tailWord_1356860
  simp only [CollatzResearch.WordTrace]
  refine ⟨24744374932167714041942017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32992499909556952055922689 24744374932167714041942017)
  ·
    refine ⟨18558281199125785531456513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24744374932167714041942017 18558281199125785531456513)
    ·
      refine ⟨13918710899344339148592385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18558281199125785531456513 13918710899344339148592385)
      ·
        refine ⟨10439033174508254361444289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13918710899344339148592385 10439033174508254361444289)
        ·
          refine ⟨7829274880881190771083217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10439033174508254361444289 7829274880881190771083217)
          ·
            refine ⟨5871956160660893078312413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829274880881190771083217 5871956160660893078312413)
            ·
              refine ⟨2201983560247834904367155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871956160660893078312413 2201983560247834904367155)
              ·
                refine ⟨3302975340371752356550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201983560247834904367155 3302975340371752356550733)
                ·
                  refine ⟨1238615752639407133706525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3302975340371752356550733 1238615752639407133706525)
                  ·
                    refine ⟨464480907239777675139947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238615752639407133706525 464480907239777675139947)
                    ·
                      rfl

theorem cell22_1356860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1356860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356860 prefixEnd_1356860 := by exact prefixLift 1356860
  have htrace : WordTrace (prefixWord ++ tailWord_1356860) baseStart_1356860 baseEnd_1356860 := by
    simpa [prefixWord, tailWord_1356860, baseEnd_1356860] using wordTrace_append hprefix tailTrace_1356860
  have hstable : (prefixWord ++ tailWord_1356860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356860).length < 2 ^ (prefixWord ++ tailWord_1356860).sum := by decide
  have hdescent : baseEnd_1356860 < baseStart_1356860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356952 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_1356952 : Nat := 118140960795 + 1356952 * 2 ^ 59
def prefixEnd_1356952 : Nat := 4983230072969 + 3 ^ 40 * 1356952 * 2
def baseEnd_1356952 : Nat := 154837466906640033946555

theorem tailTrace_1356952 : CollatzResearch.WordTrace tailWord_1356952 prefixEnd_1356952 154837466906640033946555 := by
  unfold tailWord_1356952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746052690001063898116555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32994736920001418530822073 24746052690001063898116555)
  ·
    refine ⟨37119079035001595847174833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24746052690001063898116555 37119079035001595847174833)
    ·
      refine ⟨27839309276251196885381125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37119079035001595847174833 27839309276251196885381125)
      ·
        refine ⟨5219870489297099416008961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27839309276251196885381125 5219870489297099416008961)
        ·
          refine ⟨3914902866972824562006721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219870489297099416008961 3914902866972824562006721)
          ·
            refine ⟨2936177150229618421505041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914902866972824562006721 2936177150229618421505041)
            ·
              refine ⟨2202132862672213816128781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936177150229618421505041 2202132862672213816128781)
              ·
                refine ⟨825799823502080181048293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2202132862672213816128781 825799823502080181048293)
                ·
                  refine ⟨154837466906640033946555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825799823502080181048293 154837466906640033946555)
                  ·
                    rfl

theorem cell22_1356952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_1356952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356952 prefixEnd_1356952 := by exact prefixLift 1356952
  have htrace : WordTrace (prefixWord ++ tailWord_1356952) baseStart_1356952 baseEnd_1356952 := by
    simpa [prefixWord, tailWord_1356952, baseEnd_1356952] using wordTrace_append hprefix tailTrace_1356952
  have hstable : (prefixWord ++ tailWord_1356952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356952).length < 2 ^ (prefixWord ++ tailWord_1356952).sum := by decide
  have hdescent : baseEnd_1356952 < baseStart_1356952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356954 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_1356954 : Nat := 118140960795 + 1356954 * 2 ^ 59
def prefixEnd_1356954 : Nat := 4983230072969 + 3 ^ 40 * 1356954 * 2
def baseEnd_1356954 : Nat := 464513085360792763289659

theorem tailTrace_1356954 : CollatzResearch.WordTrace tailWord_1356954 prefixEnd_1356954 464513085360792763289659 := by
  unfold tailWord_1356954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373044581498720534451479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32994785550663254758537277 12373044581498720534451479)
  ·
    refine ⟨18559566872248080801677219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12373044581498720534451479 18559566872248080801677219)
    ·
      refine ⟨27839350308372121202515829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18559566872248080801677219 27839350308372121202515829)
      ·
        refine ⟨2609939091409886362735859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27839350308372121202515829 2609939091409886362735859)
        ·
          refine ⟨3914908637114829544103789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609939091409886362735859 3914908637114829544103789)
          ·
            refine ⟨1468090738918061079038921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3914908637114829544103789 1468090738918061079038921)
            ·
              refine ⟨1101068054188545809279191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468090738918061079038921 1101068054188545809279191)
              ·
                refine ⟨1651602081282818713918787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101068054188545809279191 1651602081282818713918787)
                ·
                  refine ⟨2477403121924228070878181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651602081282818713918787 2477403121924228070878181)
                  ·
                    refine ⟨464513085360792763289659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477403121924228070878181 464513085360792763289659)
                    ·
                      rfl

theorem cell22_1356954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_1356954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356954 prefixEnd_1356954 := by exact prefixLift 1356954
  have htrace : WordTrace (prefixWord ++ tailWord_1356954) baseStart_1356954 baseEnd_1356954 := by
    simpa [prefixWord, tailWord_1356954, baseEnd_1356954] using wordTrace_append hprefix tailTrace_1356954
  have hstable : (prefixWord ++ tailWord_1356954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356954).length < 2 ^ (prefixWord ++ tailWord_1356954).sum := by decide
  have hdescent : baseEnd_1356954 < baseStart_1356954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356967 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1356967 : Nat := 118140960795 + 1356967 * 2 ^ 59
def prefixEnd_1356967 : Nat := 4983230072969 + 3 ^ 40 * 1356967 * 2
def baseEnd_1356967 : Nat := 464517535526465062714619

theorem tailTrace_1356967 : CollatzResearch.WordTrace tailWord_1356967 prefixEnd_1356967 464517535526465062714619 := by
  unfold tailWord_1356967
  simp only [CollatzResearch.WordTrace]
  refine ⟨49492652474947785358029155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32995101649965190238686103 49492652474947785358029155)
  ·
    refine ⟨74238978712421678037043733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49492652474947785358029155 74238978712421678037043733)
    ·
      refine ⟨3479952127144766157986425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74238978712421678037043733 3479952127144766157986425)
      ·
        refine ⟨2609964095358574618489819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479952127144766157986425 2609964095358574618489819)
        ·
          refine ⟨3914946143037861927734729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609964095358574618489819 3914946143037861927734729)
          ·
            refine ⟨2936209607278396445801047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914946143037861927734729 2936209607278396445801047)
            ·
              refine ⟨4404314410917594668701571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936209607278396445801047 4404314410917594668701571)
              ·
                refine ⟨6606471616376392003052357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404314410917594668701571 6606471616376392003052357)
                ·
                  refine ⟨1238713428070573500572317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6606471616376392003052357 1238713428070573500572317)
                  ·
                    refine ⟨464517535526465062714619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238713428070573500572317 464517535526465062714619)
                    ·
                      rfl

theorem cell22_1356967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1356967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1356967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1356967 prefixEnd_1356967 := by exact prefixLift 1356967
  have htrace : WordTrace (prefixWord ++ tailWord_1356967) baseStart_1356967 baseEnd_1356967 := by
    simpa [prefixWord, tailWord_1356967, baseEnd_1356967] using wordTrace_append hprefix tailTrace_1356967
  have hstable : (prefixWord ++ tailWord_1356967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356967).length < 2 ^ (prefixWord ++ tailWord_1356967).sum := by decide
  have hdescent : baseEnd_1356967 < baseStart_1356967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357014 : List Nat := [5, 2, 1, 2, 3, 1, 8]
def baseStart_1357014 : Nat := 118140960795 + 1357014 * 2 ^ 59
def prefixEnd_1357014 : Nat := 4983230072969 + 3 ^ 40 * 1357014 * 2
def baseEnd_1357014 : Nat := 17204949058776763214425

theorem tailTrace_1357014 : CollatzResearch.WordTrace tailWord_1357014 prefixEnd_1357014 17204949058776763214425 := by
  unfold tailWord_1357014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093397919111094524061881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32996244470518341589993397 3093397919111094524061881)
  ·
    refine ⟨2320048439333320893046411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093397919111094524061881 2320048439333320893046411)
    ·
      refine ⟨3480072658999981339569617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320048439333320893046411 3480072658999981339569617)
      ·
        refine ⟨2610054494249986004677213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480072658999981339569617 2610054494249986004677213)
        ·
          refine ⟨978770435343744751753955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2610054494249986004677213 978770435343744751753955)
          ·
            refine ⟨1468155653015617127630933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978770435343744751753955 1468155653015617127630933)
            ·
              refine ⟨17204949058776763214425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1468155653015617127630933 17204949058776763214425)
              ·
                rfl

theorem cell22_1357014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 8].length) (baseStart_1357014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357014 prefixEnd_1357014 := by exact prefixLift 1357014
  have htrace : WordTrace (prefixWord ++ tailWord_1357014) baseStart_1357014 baseEnd_1357014 := by
    simpa [prefixWord, tailWord_1357014, baseEnd_1357014] using wordTrace_append hprefix tailTrace_1357014
  have hstable : (prefixWord ++ tailWord_1357014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357014).length < 2 ^ (prefixWord ++ tailWord_1357014).sum := by decide
  have hdescent : baseEnd_1357014 < baseStart_1357014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357023 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_1357023 : Nat := 118140960795 + 1357023 * 2 ^ 59
def prefixEnd_1357023 : Nat := 4983230072969 + 3 ^ 40 * 1357023 * 2
def baseEnd_1357023 : Nat := 464536705470899583314447

theorem tailTrace_1357023 : CollatzResearch.WordTrace tailWord_1357023 prefixEnd_1357023 464536705470899583314447 := by
  unfold tailWord_1357023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494694962744906922067723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32996463308496604614711815 49494694962744906922067723)
  ·
    refine ⟨74242042444117360383101585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49494694962744906922067723 74242042444117360383101585)
    ·
      refine ⟨55681531833088020287326189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74242042444117360383101585 55681531833088020287326189)
      ·
        refine ⟨20880574437408007607747321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55681531833088020287326189 20880574437408007607747321)
        ·
          refine ⟨15660430828056005705810491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20880574437408007607747321 15660430828056005705810491)
          ·
            refine ⟨23490646242084008558715737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660430828056005705810491 23490646242084008558715737)
            ·
              refine ⟨17617984681563006419036803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23490646242084008558715737 17617984681563006419036803)
              ·
                refine ⟨26426977022344509628555205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17617984681563006419036803 26426977022344509628555205)
                ·
                  refine ⟨4955058191689595555354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26426977022344509628555205 4955058191689595555354101)
                  ·
                    refine ⟨464536705470899583314447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4955058191689595555354101 464536705470899583314447)
                    ·
                      rfl

theorem cell22_1357023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_1357023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357023 prefixEnd_1357023 := by exact prefixLift 1357023
  have htrace : WordTrace (prefixWord ++ tailWord_1357023) baseStart_1357023 baseEnd_1357023 := by
    simpa [prefixWord, tailWord_1357023, baseEnd_1357023] using wordTrace_append hprefix tailTrace_1357023
  have hstable : (prefixWord ++ tailWord_1357023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357023).length < 2 ^ (prefixWord ++ tailWord_1357023).sum := by decide
  have hdescent : baseEnd_1357023 < baseStart_1357023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357029 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_1357029 : Nat := 118140960795 + 1357029 * 2 ^ 59
def prefixEnd_1357029 : Nat := 4983230072969 + 3 ^ 40 * 1357029 * 2
def baseEnd_1357029 : Nat := 464538759393517567664429

theorem tailTrace_1357029 : CollatzResearch.WordTrace tailWord_1357029 prefixEnd_1357029 464538759393517567664429 := by
  unfold tailWord_1357029
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494913800723169946786141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32996609200482113297857427 49494913800723169946786141)
  ·
    refine ⟨18560592675271188730044803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49494913800723169946786141 18560592675271188730044803)
    ·
      refine ⟨27840889012906783095067205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18560592675271188730044803 27840889012906783095067205)
      ·
        refine ⟨5220166689920021830325101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27840889012906783095067205 5220166689920021830325101)
        ·
          refine ⟨1957562508720008186371913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5220166689920021830325101 1957562508720008186371913)
          ·
            refine ⟨1468171881540006139778935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1957562508720008186371913 1468171881540006139778935)
            ·
              refine ⟨2202257822310009209668403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468171881540006139778935 2202257822310009209668403)
              ·
                refine ⟨3303386733465013814502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202257822310009209668403 3303386733465013814502605)
                ·
                  refine ⟨1238770025049380180438477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3303386733465013814502605 1238770025049380180438477)
                  ·
                    refine ⟨464538759393517567664429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238770025049380180438477 464538759393517567664429)
                    ·
                      rfl

theorem cell22_1357029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_1357029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357029 prefixEnd_1357029 := by exact prefixLift 1357029
  have htrace : WordTrace (prefixWord ++ tailWord_1357029) baseStart_1357029 baseEnd_1357029 := by
    simpa [prefixWord, tailWord_1357029, baseEnd_1357029] using wordTrace_append hprefix tailTrace_1357029
  have hstable : (prefixWord ++ tailWord_1357029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357029).length < 2 ^ (prefixWord ++ tailWord_1357029).sum := by decide
  have hdescent : baseEnd_1357029 < baseStart_1357029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357042 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1357042 : Nat := 118140960795 + 1357042 * 2 ^ 59
def prefixEnd_1357042 : Nat := 4983230072969 + 3 ^ 40 * 1357042 * 2
def baseEnd_1357042 : Nat := 154847736519729955696463

theorem tailTrace_1357042 : CollatzResearch.WordTrace tailWord_1357042 prefixEnd_1357042 154847736519729955696463 := by
  unfold tailWord_1357042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373846987419018291752345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32996925299784048778006253 12373846987419018291752345)
  ·
    refine ⟨9280385240564263718814259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12373846987419018291752345 9280385240564263718814259)
    ·
      refine ⟨13920577860846395578221389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280385240564263718814259 13920577860846395578221389)
      ·
        refine ⟨5220216697817398341833021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13920577860846395578221389 5220216697817398341833021)
        ·
          refine ⟨1957581261681524378187383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5220216697817398341833021 1957581261681524378187383)
          ·
            refine ⟨2936371892522286567281075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957581261681524378187383 2936371892522286567281075)
            ·
              refine ⟨4404557838783429850921613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936371892522286567281075 4404557838783429850921613)
              ·
                refine ⟨1651709189543786194095605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4404557838783429850921613 1651709189543786194095605)
                ·
                  refine ⟨154847736519729955696463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1651709189543786194095605 154847736519729955696463)
                  ·
                    rfl

theorem cell22_1357042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1357042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357042 prefixEnd_1357042 := by exact prefixLift 1357042
  have htrace : WordTrace (prefixWord ++ tailWord_1357042) baseStart_1357042 baseEnd_1357042 := by
    simpa [prefixWord, tailWord_1357042, baseEnd_1357042] using wordTrace_append hprefix tailTrace_1357042
  have hstable : (prefixWord ++ tailWord_1357042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357042).length < 2 ^ (prefixWord ++ tailWord_1357042).sum := by decide
  have hdescent : baseEnd_1357042 < baseStart_1357042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357055 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_1357055 : Nat := 118140960795 + 1357055 * 2 ^ 59
def prefixEnd_1357055 : Nat := 4983230072969 + 3 ^ 40 * 1357055 * 2
def baseEnd_1357055 : Nat := 464547659724862166514349

theorem tailTrace_1357055 : CollatzResearch.WordTrace tailWord_1357055 prefixEnd_1357055 464547659724862166514349 := by
  unfold tailWord_1357055
  simp only [CollatzResearch.WordTrace]
  refine ⟨49495862098628976387232619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32997241399085984258155079 49495862098628976387232619)
  ·
    refine ⟨74243793147943464580848929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49495862098628976387232619 74243793147943464580848929)
    ·
      refine ⟨55682844860957598435636697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74243793147943464580848929 55682844860957598435636697)
      ·
        refine ⟨41762133645718198826727523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55682844860957598435636697 41762133645718198826727523)
        ·
          refine ⟨62643200468577298240091285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41762133645718198826727523 62643200468577298240091285)
          ·
            refine ⟨2936400021964560855004279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62643200468577298240091285 2936400021964560855004279)
            ·
              refine ⟨4404600032946841282506419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936400021964560855004279 4404600032946841282506419)
              ·
                refine ⟨6606900049420261923759629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404600032946841282506419 6606900049420261923759629)
                ·
                  refine ⟨2477587518532598221409861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6606900049420261923759629 2477587518532598221409861)
                  ·
                    refine ⟨464547659724862166514349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477587518532598221409861 464547659724862166514349)
                    ·
                      rfl

theorem cell22_1357055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_1357055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357055 prefixEnd_1357055 := by exact prefixLift 1357055
  have htrace : WordTrace (prefixWord ++ tailWord_1357055) baseStart_1357055 baseEnd_1357055 := by
    simpa [prefixWord, tailWord_1357055, baseEnd_1357055] using wordTrace_append hprefix tailTrace_1357055
  have hstable : (prefixWord ++ tailWord_1357055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357055).length < 2 ^ (prefixWord ++ tailWord_1357055).sum := by decide
  have hdescent : baseEnd_1357055 < baseStart_1357055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357083 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_1357083 : Nat := 118140960795 + 1357083 * 2 ^ 59
def prefixEnd_1357083 : Nat := 4983230072969 + 3 ^ 40 * 1357083 * 2
def baseEnd_1357083 : Nat := 464557244697079426814263

theorem tailTrace_1357083 : CollatzResearch.WordTrace tailWord_1357083 prefixEnd_1357083 464557244697079426814263 := by
  unfold tailWord_1357083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49496883342527537169251903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32997922228351691446167935 49496883342527537169251903)
  ·
    refine ⟨74245325013791305753877855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49496883342527537169251903 74245325013791305753877855)
    ·
      refine ⟨111367987520686958630816783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74245325013791305753877855 111367987520686958630816783)
      ·
        refine ⟨167051981281030437946225175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111367987520686958630816783 167051981281030437946225175)
        ·
          refine ⟨250577971921545656919337763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167051981281030437946225175 250577971921545656919337763)
          ·
            refine ⟨375866957882318485379006645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250577971921545656919337763 375866957882318485379006645)
            ·
              refine ⟨35237527301467358004281873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 375866957882318485379006645 35237527301467358004281873)
              ·
                refine ⟨26428145476100518503211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35237527301467358004281873 26428145476100518503211405)
                ·
                  refine ⟨9910554553537694438704277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26428145476100518503211405 9910554553537694438704277)
                  ·
                    refine ⟨464557244697079426814263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9910554553537694438704277 464557244697079426814263)
                    ·
                      rfl

theorem cell22_1357083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_1357083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357083 prefixEnd_1357083 := by exact prefixLift 1357083
  have htrace : WordTrace (prefixWord ++ tailWord_1357083) baseStart_1357083 baseEnd_1357083 := by
    simpa [prefixWord, tailWord_1357083, baseEnd_1357083] using wordTrace_append hprefix tailTrace_1357083
  have hstable : (prefixWord ++ tailWord_1357083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357083).length < 2 ^ (prefixWord ++ tailWord_1357083).sum := by decide
  have hdescent : baseEnd_1357083 < baseStart_1357083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357166 : List Nat := [4, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1357166 : Nat := 118140960795 + 1357166 * 2 ^ 59
def prefixEnd_1357166 : Nat := 4983230072969 + 3 ^ 40 * 1357166 * 2
def baseEnd_1357166 : Nat := 51620628588143875221001

theorem tailTrace_1357166 : CollatzResearch.WordTrace tailWord_1357166 prefixEnd_1357166 51620628588143875221001 := by
  unfold tailWord_1357166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187488825153355293065419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32999940400817894896348901 6187488825153355293065419)
  ·
    refine ⟨9281233237730032939598129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6187488825153355293065419 9281233237730032939598129)
    ·
      refine ⟨6960924928297524704698597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9281233237730032939598129 6960924928297524704698597)
      ·
        refine ⟨1305173424055785882130987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6960924928297524704698597 1305173424055785882130987)
        ·
          refine ⟨1957760136083678823196481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305173424055785882130987 1957760136083678823196481)
          ·
            refine ⟨1468320102062759117397361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1957760136083678823196481 1468320102062759117397361)
            ·
              refine ⟨1101240076547069338048021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468320102062759117397361 1101240076547069338048021)
              ·
                refine ⟨51620628588143875221001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1101240076547069338048021 51620628588143875221001)
                ·
                  rfl

theorem cell22_1357166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1357166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357166 prefixEnd_1357166 := by exact prefixLift 1357166
  have htrace : WordTrace (prefixWord ++ tailWord_1357166) baseStart_1357166 baseEnd_1357166 := by
    simpa [prefixWord, tailWord_1357166, baseEnd_1357166] using wordTrace_append hprefix tailTrace_1357166
  have hstable : (prefixWord ++ tailWord_1357166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357166).length < 2 ^ (prefixWord ++ tailWord_1357166).sum := by decide
  have hdescent : baseEnd_1357166 < baseStart_1357166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357198 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1357198 : Nat := 118140960795 + 1357198 * 2 ^ 59
def prefixEnd_1357198 : Nat := 4983230072969 + 3 ^ 40 * 1357198 * 2
def baseEnd_1357198 : Nat := 464596611547257460188911

theorem tailTrace_1357198 : CollatzResearch.WordTrace tailWord_1357198 prefixEnd_1357198 464596611547257460188911 := by
  unfold tailWord_1357198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187634717138863976211031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33000718491407274539792165 6187634717138863976211031)
  ·
    refine ⟨9281452075708295964316547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6187634717138863976211031 9281452075708295964316547)
    ·
      refine ⟨13922178113562443946474821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9281452075708295964316547 13922178113562443946474821)
      ·
        refine ⟨2610408396292958239964029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13922178113562443946474821 2610408396292958239964029)
        ·
          refine ⟨978903148609859339986511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2610408396292958239964029 978903148609859339986511)
          ·
            refine ⟨1468354722914789009979767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978903148609859339986511 1468354722914789009979767)
            ·
              refine ⟨2202532084372183514969651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468354722914789009979767 2202532084372183514969651)
              ·
                refine ⟨3303798126558275272454477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202532084372183514969651 3303798126558275272454477)
                ·
                  refine ⟨1238924297459353227170429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3303798126558275272454477 1238924297459353227170429)
                  ·
                    refine ⟨464596611547257460188911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238924297459353227170429 464596611547257460188911)
                    ·
                      rfl

theorem cell22_1357198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1357198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357198 prefixEnd_1357198 := by exact prefixLift 1357198
  have htrace : WordTrace (prefixWord ++ tailWord_1357198) baseStart_1357198 baseEnd_1357198 := by
    simpa [prefixWord, tailWord_1357198, baseEnd_1357198] using wordTrace_append hprefix tailTrace_1357198
  have hstable : (prefixWord ++ tailWord_1357198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357198).length < 2 ^ (prefixWord ++ tailWord_1357198).sum := by decide
  have hdescent : baseEnd_1357198 < baseStart_1357198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357235 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_1357235 : Nat := 118140960795 + 1357235 * 2 ^ 59
def prefixEnd_1357235 : Nat := 4983230072969 + 3 ^ 40 * 1357235 * 2
def baseEnd_1357235 : Nat := 464609277403401697013797

theorem tailTrace_1357235 : CollatzResearch.WordTrace tailWord_1357235 prefixEnd_1357235 464609277403401697013797 := by
  unfold tailWord_1357235
  simp only [CollatzResearch.WordTrace]
  refine ⟨49502427237976867128785159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33001618158651244752523439 49502427237976867128785159)
  ·
    refine ⟨74253640856965300693177739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49502427237976867128785159 74253640856965300693177739)
    ·
      refine ⟨111380461285447951039766609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74253640856965300693177739 111380461285447951039766609)
      ·
        refine ⟨83535345964085963279824957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111380461285447951039766609 83535345964085963279824957)
        ·
          refine ⟨31325754736532236229934359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83535345964085963279824957 31325754736532236229934359)
          ·
            refine ⟨46988632104798354344901539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31325754736532236229934359 46988632104798354344901539)
            ·
              refine ⟨70482948157197531517352309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46988632104798354344901539 70482948157197531517352309)
              ·
                refine ⟨6607776389737268579751779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70482948157197531517352309 6607776389737268579751779)
                ·
                  refine ⟨9911664584605902869627669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607776389737268579751779 9911664584605902869627669)
                  ·
                    refine ⟨464609277403401697013797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9911664584605902869627669 464609277403401697013797)
                    ·
                      rfl

theorem cell22_1357235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_1357235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357235 prefixEnd_1357235 := by exact prefixLift 1357235
  have htrace : WordTrace (prefixWord ++ tailWord_1357235) baseStart_1357235 baseEnd_1357235 := by
    simpa [prefixWord, tailWord_1357235, baseEnd_1357235] using wordTrace_append hprefix tailTrace_1357235
  have hstable : (prefixWord ++ tailWord_1357235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357235).length < 2 ^ (prefixWord ++ tailWord_1357235).sum := by decide
  have hdescent : baseEnd_1357235 < baseStart_1357235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357237 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1357237 : Nat := 118140960795 + 1357237 * 2 ^ 59
def prefixEnd_1357237 : Nat := 4983230072969 + 3 ^ 40 * 1357237 * 2
def baseEnd_1357237 : Nat := 464609962044274358463791

theorem tailTrace_1357237 : CollatzResearch.WordTrace tailWord_1357237 prefixEnd_1357237 464609962044274358463791 := by
  unfold tailWord_1357237
  simp only [CollatzResearch.WordTrace]
  refine ⟨49502500183969621470357965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33001666789313080980238643 49502500183969621470357965)
  ·
    refine ⟨18563437568988608051384237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49502500183969621470357965 18563437568988608051384237)
    ·
      refine ⟨6961289088370728019269089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18563437568988608051384237 6961289088370728019269089)
      ·
        refine ⟨5220966816278046014451817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6961289088370728019269089 5220966816278046014451817)
        ·
          refine ⟨3915725112208534510838863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5220966816278046014451817 3915725112208534510838863)
          ·
            refine ⟨5873587668312801766258295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915725112208534510838863 5873587668312801766258295)
            ·
              refine ⟨8810381502469202649387443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873587668312801766258295 8810381502469202649387443)
              ·
                refine ⟨13215572253703803974081165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810381502469202649387443 13215572253703803974081165)
                ·
                  refine ⟨4955839595138926490280437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13215572253703803974081165 4955839595138926490280437)
                  ·
                    refine ⟨464609962044274358463791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4955839595138926490280437 464609962044274358463791)
                    ·
                      rfl

theorem cell22_1357237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1357237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357237 prefixEnd_1357237 := by exact prefixLift 1357237
  have htrace : WordTrace (prefixWord ++ tailWord_1357237) baseStart_1357237 baseEnd_1357237 := by
    simpa [prefixWord, tailWord_1357237, baseEnd_1357237] using wordTrace_append hprefix tailTrace_1357237
  have hstable : (prefixWord ++ tailWord_1357237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357237).length < 2 ^ (prefixWord ++ tailWord_1357237).sum := by decide
  have hdescent : baseEnd_1357237 < baseStart_1357237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357241 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_1357241 : Nat := 118140960795 + 1357241 * 2 ^ 59
def prefixEnd_1357241 : Nat := 4983230072969 + 3 ^ 40 * 1357241 * 2
def baseEnd_1357241 : Nat := 464611331326019681363779

theorem tailTrace_1357241 : CollatzResearch.WordTrace tailWord_1357241 prefixEnd_1357241 464611331326019681363779 := by
  unfold tailWord_1357241
  simp only [CollatzResearch.WordTrace]
  refine ⟨49502646075955130153503577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33001764050636753435669051 49502646075955130153503577)
  ·
    refine ⟨37126984556966347615127683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49502646075955130153503577 37126984556966347615127683)
    ·
      refine ⟨55690476835449521422691525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37126984556966347615127683 55690476835449521422691525)
      ·
        refine ⟨10441964406646785266754661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55690476835449521422691525 10441964406646785266754661)
        ·
          refine ⟨1957868326246272237516499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10441964406646785266754661 1957868326246272237516499)
          ·
            refine ⟨2936802489369408356274749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957868326246272237516499 2936802489369408356274749)
            ·
              refine ⟨1101300933513528133603031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936802489369408356274749 1101300933513528133603031)
              ·
                refine ⟨1651951400270292200404547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101300933513528133603031 1651951400270292200404547)
                ·
                  refine ⟨2477927100405438300606821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651951400270292200404547 2477927100405438300606821)
                  ·
                    refine ⟨464611331326019681363779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477927100405438300606821 464611331326019681363779)
                    ·
                      rfl

theorem cell22_1357241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_1357241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357241 prefixEnd_1357241 := by exact prefixLift 1357241
  have htrace : WordTrace (prefixWord ++ tailWord_1357241) baseStart_1357241 baseEnd_1357241 := by
    simpa [prefixWord, tailWord_1357241, baseEnd_1357241] using wordTrace_append hprefix tailTrace_1357241
  have hstable : (prefixWord ++ tailWord_1357241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357241).length < 2 ^ (prefixWord ++ tailWord_1357241).sum := by decide
  have hdescent : baseEnd_1357241 < baseStart_1357241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357265 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_1357265 : Nat := 118140960795 + 1357265 * 2 ^ 59
def prefixEnd_1357265 : Nat := 4983230072969 + 3 ^ 40 * 1357265 * 2
def baseEnd_1357265 : Nat := 464619547016491618763705

theorem tailTrace_1357265 : CollatzResearch.WordTrace tailWord_1357265 prefixEnd_1357265 464619547016491618763705 := by
  unfold tailWord_1357265
  simp only [CollatzResearch.WordTrace]
  refine ⟨49503521427868182252377249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33002347618578788168251499 49503521427868182252377249)
  ·
    refine ⟨37127641070901136689282937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49503521427868182252377249 37127641070901136689282937)
    ·
      refine ⟨27845730803175852516962203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37127641070901136689282937 27845730803175852516962203)
      ·
        refine ⟨41768596204763778775443305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27845730803175852516962203 41768596204763778775443305)
        ·
          refine ⟨31326447153572834081582479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41768596204763778775443305 31326447153572834081582479)
          ·
            refine ⟨46989670730359251122373719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31326447153572834081582479 46989670730359251122373719)
            ·
              refine ⟨70484506095538876683560579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46989670730359251122373719 70484506095538876683560579)
              ·
                refine ⟨105726759143308315025340869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70484506095538876683560579 105726759143308315025340869)
                ·
                  refine ⟨19823767339370309067251413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105726759143308315025340869 19823767339370309067251413)
                  ·
                    refine ⟨464619547016491618763705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19823767339370309067251413 464619547016491618763705)
                    ·
                      rfl

theorem cell22_1357265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_1357265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357265 prefixEnd_1357265 := by exact prefixLift 1357265
  have htrace : WordTrace (prefixWord ++ tailWord_1357265) baseStart_1357265 baseEnd_1357265 := by
    simpa [prefixWord, tailWord_1357265, baseEnd_1357265] using wordTrace_append hprefix tailTrace_1357265
  have hstable : (prefixWord ++ tailWord_1357265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357265).length < 2 ^ (prefixWord ++ tailWord_1357265).sum := by decide
  have hdescent : baseEnd_1357265 < baseStart_1357265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357329 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 5]
def baseStart_1357329 : Nat := 118140960795 + 1357329 * 2 ^ 59
def prefixEnd_1357329 : Nat := 4983230072969 + 3 ^ 40 * 1357329 * 2
def baseEnd_1357329 : Nat := 154880485174805595054503

theorem tailTrace_1357329 : CollatzResearch.WordTrace tailWord_1357329 prefixEnd_1357329 154880485174805595054503 := by
  unfold tailWord_1357329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49505855699636321182707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33003903799757547455138027 49505855699636321182707041)
  ·
    refine ⟨37129391774727240887030281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49505855699636321182707041 37129391774727240887030281)
    ·
      refine ⟨27847043831045430665272711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37129391774727240887030281 27847043831045430665272711)
      ·
        refine ⟨41770565746568145997909067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847043831045430665272711 41770565746568145997909067)
        ·
          refine ⟨62655848619852218996863601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41770565746568145997909067 62655848619852218996863601)
          ·
            refine ⟨46991886464889164247647701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62655848619852218996863601 46991886464889164247647701)
            ·
              refine ⟨1101372339020839787054243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46991886464889164247647701 1101372339020839787054243)
              ·
                refine ⟨1652058508531259680581365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101372339020839787054243 1652058508531259680581365)
                ·
                  refine ⟨154880485174805595054503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652058508531259680581365 154880485174805595054503)
                  ·
                    rfl

theorem cell22_1357329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_1357329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357329 prefixEnd_1357329 := by exact prefixLift 1357329
  have htrace : WordTrace (prefixWord ++ tailWord_1357329) baseStart_1357329 baseEnd_1357329 := by
    simpa [prefixWord, tailWord_1357329, baseEnd_1357329] using wordTrace_append hprefix tailTrace_1357329
  have hstable : (prefixWord ++ tailWord_1357329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357329).length < 2 ^ (prefixWord ++ tailWord_1357329).sum := by decide
  have hdescent : baseEnd_1357329 < baseStart_1357329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357387 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_1357387 : Nat := 118140960795 + 1357387 * 2 ^ 59
def prefixEnd_1357387 : Nat := 4983230072969 + 3 ^ 40 * 1357387 * 2
def baseEnd_1357387 : Nat := 464661310109723967213331

theorem tailTrace_1357387 : CollatzResearch.WordTrace tailWord_1357387 prefixEnd_1357387 464661310109723967213331 := by
  unfold tailWord_1357387
  simp only [CollatzResearch.WordTrace]
  refine ⟨49507971133426197088318415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33005314088950798058878943 49507971133426197088318415)
  ·
    refine ⟨74261956700139295632477623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49507971133426197088318415 74261956700139295632477623)
    ·
      refine ⟨111392935050208943448716435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74261956700139295632477623 111392935050208943448716435)
      ·
        refine ⟨167089402575313415173074653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111392935050208943448716435 167089402575313415173074653)
        ·
          refine ⟨62658525965742530689902995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167089402575313415173074653 62658525965742530689902995)
          ·
            refine ⟨93987788948613796034854493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62658525965742530689902995 93987788948613796034854493)
            ·
              refine ⟨35245420855730173513070435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93987788948613796034854493 35245420855730173513070435)
              ·
                refine ⟨52868131283595260269605653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35245420855730173513070435 52868131283595260269605653)
                ·
                  refine ⟨2478193653918527825137765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52868131283595260269605653 2478193653918527825137765)
                  ·
                    refine ⟨464661310109723967213331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478193653918527825137765 464661310109723967213331)
                    ·
                      rfl

theorem cell22_1357387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_1357387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357387 prefixEnd_1357387 := by exact prefixLift 1357387
  have htrace : WordTrace (prefixWord ++ tailWord_1357387) baseStart_1357387 baseEnd_1357387 := by
    simpa [prefixWord, tailWord_1357387, baseEnd_1357387] using wordTrace_append hprefix tailTrace_1357387
  have hstable : (prefixWord ++ tailWord_1357387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357387).length < 2 ^ (prefixWord ++ tailWord_1357387).sum := by decide
  have hdescent : baseEnd_1357387 < baseStart_1357387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357511 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1357511 : Nat := 118140960795 + 1357511 * 2 ^ 59
def prefixEnd_1357511 : Nat := 4983230072969 + 3 ^ 40 * 1357511 * 2
def baseEnd_1357511 : Nat := 464703757843828977112951

theorem tailTrace_1357511 : CollatzResearch.WordTrace tailWord_1357511 prefixEnd_1357511 464703757843828977112951 := by
  unfold tailWord_1357511
  simp only [CollatzResearch.WordTrace]
  refine ⟨49512493784976966265832387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33008329189984644177221591 49512493784976966265832387)
  ·
    refine ⟨74268740677465449398748581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49512493784976966265832387 74268740677465449398748581)
    ·
      refine ⟨13925388877024771762265359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74268740677465449398748581 13925388877024771762265359)
      ·
        refine ⟨20888083315537157643398039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925388877024771762265359 20888083315537157643398039)
        ·
          refine ⟨31332124973305736465097059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888083315537157643398039 31332124973305736465097059)
          ·
            refine ⟨46998187459958604697645589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31332124973305736465097059 46998187459958604697645589)
            ·
              refine ⟨2203040037185559595202137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46998187459958604697645589 2203040037185559595202137)
              ·
                refine ⟨1652280027889169696401603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203040037185559595202137 1652280027889169696401603)
                ·
                  refine ⟨2478420041833754544602405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652280027889169696401603 2478420041833754544602405)
                  ·
                    refine ⟨464703757843828977112951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478420041833754544602405 464703757843828977112951)
                    ·
                      rfl

theorem cell22_1357511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1357511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357511 prefixEnd_1357511 := by exact prefixLift 1357511
  have htrace : WordTrace (prefixWord ++ tailWord_1357511) baseStart_1357511 baseEnd_1357511 := by
    simpa [prefixWord, tailWord_1357511, baseEnd_1357511] using wordTrace_append hprefix tailTrace_1357511
  have hstable : (prefixWord ++ tailWord_1357511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357511).length < 2 ^ (prefixWord ++ tailWord_1357511).sum := by decide
  have hdescent : baseEnd_1357511 < baseStart_1357511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357541 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_1357541 : Nat := 118140960795 + 1357541 * 2 ^ 59
def prefixEnd_1357541 : Nat := 4983230072969 + 3 ^ 40 * 1357541 * 2
def baseEnd_1357541 : Nat := 464714027456918898862859

theorem tailTrace_1357541 : CollatzResearch.WordTrace tailWord_1357541 prefixEnd_1357541 464714027456918898862859 := by
  unfold tailWord_1357541
  simp only [CollatzResearch.WordTrace]
  refine ⟨49513587974868281389424477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33009058649912187592949651 49513587974868281389424477)
  ·
    refine ⟨18567595490575605521034179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49513587974868281389424477 18567595490575605521034179)
    ·
      refine ⟨27851393235863408281551269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18567595490575605521034179 27851393235863408281551269)
      ·
        refine ⟨5222136231724389052790863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27851393235863408281551269 5222136231724389052790863)
        ·
          refine ⟨7833204347586583579186295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222136231724389052790863 7833204347586583579186295)
          ·
            refine ⟨11749806521379875368779443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833204347586583579186295 11749806521379875368779443)
            ·
              refine ⟨17624709782069813053169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11749806521379875368779443 17624709782069813053169165)
              ·
                refine ⟨6609266168276179894938437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17624709782069813053169165 6609266168276179894938437)
                ·
                  refine ⟨1239237406551783730300957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6609266168276179894938437 1239237406551783730300957)
                  ·
                    refine ⟨464714027456918898862859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239237406551783730300957 464714027456918898862859)
                    ·
                      rfl

theorem cell22_1357541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_1357541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357541 prefixEnd_1357541 := by exact prefixLift 1357541
  have htrace : WordTrace (prefixWord ++ tailWord_1357541) baseStart_1357541 baseEnd_1357541 := by
    simpa [prefixWord, tailWord_1357541, baseEnd_1357541] using wordTrace_append hprefix tailTrace_1357541
  have hstable : (prefixWord ++ tailWord_1357541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357541).length < 2 ^ (prefixWord ++ tailWord_1357541).sum := by decide
  have hdescent : baseEnd_1357541 < baseStart_1357541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357569 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1357569 : Nat := 118140960795 + 1357569 * 2 ^ 59
def prefixEnd_1357569 : Nat := 4983230072969 + 3 ^ 40 * 1357569 * 2
def baseEnd_1357569 : Nat := 464723612429136159162773

theorem tailTrace_1357569 : CollatzResearch.WordTrace tailWord_1357569 prefixEnd_1357569 464723612429136159162773 := by
  unfold tailWord_1357569
  simp only [CollatzResearch.WordTrace]
  refine ⟨49514609218766842171443761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33009739479177894780962507 49514609218766842171443761)
  ·
    refine ⟨37135956914075131628582821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49514609218766842171443761 37135956914075131628582821)
    ·
      refine ⟨6962991921389087180359279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37135956914075131628582821 6962991921389087180359279)
      ·
        refine ⟨10444487882083630770538919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962991921389087180359279 10444487882083630770538919)
        ·
          refine ⟨15666731823125446155808379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10444487882083630770538919 15666731823125446155808379)
          ·
            refine ⟨23500097734688169233712569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15666731823125446155808379 23500097734688169233712569)
            ·
              refine ⟨17625073301016126925284427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23500097734688169233712569 17625073301016126925284427)
              ·
                refine ⟨26437609951524190387926641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17625073301016126925284427 26437609951524190387926641)
                ·
                  refine ⟨19828207463643142790944981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26437609951524190387926641 19828207463643142790944981)
                  ·
                    refine ⟨464723612429136159162773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19828207463643142790944981 464723612429136159162773)
                    ·
                      rfl

theorem cell22_1357569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1357569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357569 prefixEnd_1357569 := by exact prefixLift 1357569
  have htrace : WordTrace (prefixWord ++ tailWord_1357569) baseStart_1357569 baseEnd_1357569 := by
    simpa [prefixWord, tailWord_1357569, baseEnd_1357569] using wordTrace_append hprefix tailTrace_1357569
  have hstable : (prefixWord ++ tailWord_1357569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357569).length < 2 ^ (prefixWord ++ tailWord_1357569).sum := by decide
  have hdescent : baseEnd_1357569 < baseStart_1357569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357588 : List Nat := [2, 4, 4, 1, 11]
def baseStart_1357588 : Nat := 118140960795 + 1357588 * 2 ^ 59
def prefixEnd_1357588 : Nat := 4983230072969 + 3 ^ 40 * 1357588 * 2
def baseEnd_1357588 : Nat := 1912469615298051205505

theorem tailTrace_1357588 : CollatzResearch.WordTrace tailWord_1357588 prefixEnd_1357588 1912469615298051205505 := by
  unfold tailWord_1357588
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757651102849004208192709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33010201470465338944256945 24757651102849004208192709)
  ·
    refine ⟨4642059581784188289036133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24757651102849004208192709 4642059581784188289036133)
    ·
      refine ⟨870386171584535304194275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4642059581784188289036133 870386171584535304194275)
      ·
        refine ⟨1305579257376802956291413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870386171584535304194275 1305579257376802956291413)
        ·
          refine ⟨1912469615298051205505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1305579257376802956291413 1912469615298051205505)
          ·
            rfl

theorem cell22_1357588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 11].length) (baseStart_1357588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357588 prefixEnd_1357588 := by exact prefixLift 1357588
  have htrace : WordTrace (prefixWord ++ tailWord_1357588) baseStart_1357588 baseEnd_1357588 := by
    simpa [prefixWord, tailWord_1357588, baseEnd_1357588] using wordTrace_append hprefix tailTrace_1357588
  have hstable : (prefixWord ++ tailWord_1357588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357588).length < 2 ^ (prefixWord ++ tailWord_1357588).sum := by decide
  have hdescent : baseEnd_1357588 < baseStart_1357588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357620 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1357620 : Nat := 118140960795 + 1357620 * 2 ^ 59
def prefixEnd_1357620 : Nat := 4983230072969 + 3 ^ 40 * 1357620 * 2
def baseEnd_1357620 : Nat := 464741070771389026137617

theorem tailTrace_1357620 : CollatzResearch.WordTrace tailWord_1357620 prefixEnd_1357620 464741070771389026137617 := by
  unfold tailWord_1357620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758234670791038940775157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33010979561054718587700209 24758234670791038940775157)
  ·
    refine ⟨2321084500386659900697671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24758234670791038940775157 2321084500386659900697671)
    ·
      refine ⟨3481626750579989851046507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321084500386659900697671 3481626750579989851046507)
      ·
        refine ⟨5222440125869984776569761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481626750579989851046507 5222440125869984776569761)
        ·
          refine ⟨3916830094402488582427321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5222440125869984776569761 3916830094402488582427321)
          ·
            refine ⟨2937622570801866436820491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3916830094402488582427321 2937622570801866436820491)
            ·
              refine ⟨4406433856202799655230737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937622570801866436820491 4406433856202799655230737)
              ·
                refine ⟨3304825392152099741423053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406433856202799655230737 3304825392152099741423053)
                ·
                  refine ⟨1239309522057037403033645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3304825392152099741423053 1239309522057037403033645)
                  ·
                    refine ⟨464741070771389026137617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239309522057037403033645 464741070771389026137617)
                    ·
                      rfl

theorem cell22_1357620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1357620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357620 prefixEnd_1357620 := by exact prefixLift 1357620
  have htrace : WordTrace (prefixWord ++ tailWord_1357620) baseStart_1357620 baseEnd_1357620 := by
    simpa [prefixWord, tailWord_1357620, baseEnd_1357620] using wordTrace_append hprefix tailTrace_1357620
  have hstable : (prefixWord ++ tailWord_1357620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357620).length < 2 ^ (prefixWord ++ tailWord_1357620).sum := by decide
  have hdescent : baseEnd_1357620 < baseStart_1357620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357678 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1357678 : Nat := 118140960795 + 1357678 * 2 ^ 59
def prefixEnd_1357678 : Nat := 4983230072969 + 3 ^ 40 * 1357678 * 2
def baseEnd_1357678 : Nat := 154920308452232069395813

theorem tailTrace_1357678 : CollatzResearch.WordTrace tailWord_1357678 prefixEnd_1357678 154920308452232069395813 := by
  unfold tailWord_1357678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189823096921494223395211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33012389850247969191441125 6189823096921494223395211)
  ·
    refine ⟨9284734645382241335092817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6189823096921494223395211 9284734645382241335092817)
    ·
      refine ⟨6963550984036681001319613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9284734645382241335092817 6963550984036681001319613)
      ·
        refine ⟨2611331619013755375494855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6963550984036681001319613 2611331619013755375494855)
        ·
          refine ⟨3916997428520633063242283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611331619013755375494855 3916997428520633063242283)
          ·
            refine ⟨5875496142780949594863425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916997428520633063242283 5875496142780949594863425)
            ·
              refine ⟨4406622107085712196147569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875496142780949594863425 4406622107085712196147569)
              ·
                refine ⟨3304966580314284147110677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406622107085712196147569 3304966580314284147110677)
                ·
                  refine ⟨154920308452232069395813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3304966580314284147110677 154920308452232069395813)
                  ·
                    rfl

theorem cell22_1357678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1357678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357678 prefixEnd_1357678 := by exact prefixLift 1357678
  have htrace : WordTrace (prefixWord ++ tailWord_1357678) baseStart_1357678 baseEnd_1357678 := by
    simpa [prefixWord, tailWord_1357678, baseEnd_1357678] using wordTrace_append hprefix tailTrace_1357678
  have hstable : (prefixWord ++ tailWord_1357678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357678).length < 2 ^ (prefixWord ++ tailWord_1357678).sum := by decide
  have hdescent : baseEnd_1357678 < baseStart_1357678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357691 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_1357691 : Nat := 118140960795 + 1357691 * 2 ^ 59
def prefixEnd_1357691 : Nat := 4983230072969 + 3 ^ 40 * 1357691 * 2
def baseEnd_1357691 : Nat := 464765375522368507612399

theorem tailTrace_1357691 : CollatzResearch.WordTrace tailWord_1357691 prefixEnd_1357691 464765375522368507612399 := by
  unfold tailWord_1357691
  simp only [CollatzResearch.WordTrace]
  refine ⟨49519058924324857007384927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33012705949549904671589951 49519058924324857007384927)
  ·
    refine ⟨74278588386487285511077391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49519058924324857007384927 74278588386487285511077391)
    ·
      refine ⟨111417882579730928266616087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74278588386487285511077391 111417882579730928266616087)
      ·
        refine ⟨167126823869596392399924131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111417882579730928266616087 167126823869596392399924131)
        ·
          refine ⟨250690235804394588599886197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167126823869596392399924131 250690235804394588599886197)
          ·
            refine ⟨23502209606661992681239331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250690235804394588599886197 23502209606661992681239331)
            ·
              refine ⟨35253314409992989021858997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23502209606661992681239331 35253314409992989021858997)
              ·
                refine ⟨3304998225936842720799281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35253314409992989021858997 3304998225936842720799281)
                ·
                  refine ⟨2478748669452632040599461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3304998225936842720799281 2478748669452632040599461)
                  ·
                    refine ⟨464765375522368507612399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478748669452632040599461 464765375522368507612399)
                    ·
                      rfl

theorem cell22_1357691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_1357691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357691 prefixEnd_1357691 := by exact prefixLift 1357691
  have htrace : WordTrace (prefixWord ++ tailWord_1357691) baseStart_1357691 baseEnd_1357691 := by
    simpa [prefixWord, tailWord_1357691, baseEnd_1357691] using wordTrace_append hprefix tailTrace_1357691
  have hstable : (prefixWord ++ tailWord_1357691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357691).length < 2 ^ (prefixWord ++ tailWord_1357691).sum := by decide
  have hdescent : baseEnd_1357691 < baseStart_1357691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357768 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_1357768 : Nat := 118140960795 + 1357768 * 2 ^ 59
def prefixEnd_1357768 : Nat := 4983230072969 + 3 ^ 40 * 1357768 * 2
def baseEnd_1357768 : Nat := 154930578065321991145721

theorem tailTrace_1357768 : CollatzResearch.WordTrace tailWord_1357768 prefixEnd_1357768 154930578065321991145721 := by
  unfold tailWord_1357768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24760933672522949578968979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33014578230030599438625305 24760933672522949578968979)
  ·
    refine ⟨37141400508784424368453469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24760933672522949578968979 37141400508784424368453469)
    ·
      refine ⟨13928025190794159138170051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37141400508784424368453469 13928025190794159138170051)
      ·
        refine ⟨20892037786191238707255077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13928025190794159138170051 20892037786191238707255077)
        ·
          refine ⟨3917257084910857257610327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20892037786191238707255077 3917257084910857257610327)
          ·
            refine ⟨5875885627366285886415491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917257084910857257610327 5875885627366285886415491)
            ·
              refine ⟨8813828441049428829623237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875885627366285886415491 8813828441049428829623237)
              ·
                refine ⟨1652592832696767905554357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8813828441049428829623237 1652592832696767905554357)
                ·
                  refine ⟨154930578065321991145721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652592832696767905554357 154930578065321991145721)
                  ·
                    rfl

theorem cell22_1357768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_1357768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357768 prefixEnd_1357768 := by exact prefixLift 1357768
  have htrace : WordTrace (prefixWord ++ tailWord_1357768) baseStart_1357768 baseEnd_1357768 := by
    simpa [prefixWord, tailWord_1357768, baseEnd_1357768] using wordTrace_append hprefix tailTrace_1357768
  have hstable : (prefixWord ++ tailWord_1357768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357768).length < 2 ^ (prefixWord ++ tailWord_1357768).sum := by decide
  have hdescent : baseEnd_1357768 < baseStart_1357768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357772 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_1357772 : Nat := 118140960795 + 1357772 * 2 ^ 59
def prefixEnd_1357772 : Nat := 4983230072969 + 3 ^ 40 * 1357772 * 2
def baseEnd_1357772 : Nat := 464793103477711296337151

theorem tailTrace_1357772 : CollatzResearch.WordTrace tailWord_1357772 prefixEnd_1357772 464793103477711296337151 := by
  unfold tailWord_1357772
  simp only [CollatzResearch.WordTrace]
  refine ⟨24761006618515703920541785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33014675491354271894055713 24761006618515703920541785)
  ·
    refine ⟨18570754963886777940406339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24761006618515703920541785 18570754963886777940406339)
    ·
      refine ⟨27856132445830166910609509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18570754963886777940406339 27856132445830166910609509)
      ·
        refine ⟨5223024833593156295739283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27856132445830166910609509 5223024833593156295739283)
        ·
          refine ⟨7834537250389734443608925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223024833593156295739283 7834537250389734443608925)
          ·
            refine ⟨2937951468896150416353347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7834537250389734443608925 2937951468896150416353347)
            ·
              refine ⟨4406927203344225624530021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937951468896150416353347 4406927203344225624530021)
              ·
                refine ⟨826298850627042304599379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4406927203344225624530021 826298850627042304599379)
                ·
                  refine ⟨1239448275940563456899069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826298850627042304599379 1239448275940563456899069)
                  ·
                    refine ⟨464793103477711296337151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239448275940563456899069 464793103477711296337151)
                    ·
                      rfl

theorem cell22_1357772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_1357772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357772 prefixEnd_1357772 := by exact prefixLift 1357772
  have htrace : WordTrace (prefixWord ++ tailWord_1357772) baseStart_1357772 baseEnd_1357772 := by
    simpa [prefixWord, tailWord_1357772, baseEnd_1357772] using wordTrace_append hprefix tailTrace_1357772
  have hstable : (prefixWord ++ tailWord_1357772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357772).length < 2 ^ (prefixWord ++ tailWord_1357772).sum := by decide
  have hdescent : baseEnd_1357772 < baseStart_1357772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357858 : List Nat := [3, 3, 1, 1, 1, 2, 3, 8]
def baseStart_1357858 : Nat := 118140960795 + 1357858 * 2 ^ 59
def prefixEnd_1357858 : Nat := 4983230072969 + 3 ^ 40 * 1357858 * 2
def baseEnd_1357858 : Nat := 51646949226137304298543

theorem tailTrace_1357858 : CollatzResearch.WordTrace tailWord_1357858 prefixEnd_1357858 51646949226137304298543 := by
  unfold tailWord_1357858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381287478679961132178557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33016766609813229685809485 12381287478679961132178557)
  ·
    refine ⟨4642982804504985424566959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12381287478679961132178557 4642982804504985424566959)
    ·
      refine ⟨6964474206757478136850439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4642982804504985424566959 6964474206757478136850439)
      ·
        refine ⟨10446711310136217205275659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964474206757478136850439 10446711310136217205275659)
        ·
          refine ⟨15670066965204325807913489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10446711310136217205275659 15670066965204325807913489)
          ·
            refine ⟨11752550223903244355935117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15670066965204325807913489 11752550223903244355935117)
            ·
              refine ⟨4407206333963716633475669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11752550223903244355935117 4407206333963716633475669)
              ·
                refine ⟨51646949226137304298543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4407206333963716633475669 51646949226137304298543)
                ·
                  rfl

theorem cell22_1357858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_1357858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357858 prefixEnd_1357858 := by exact prefixLift 1357858
  have htrace : WordTrace (prefixWord ++ tailWord_1357858) baseStart_1357858 baseEnd_1357858 := by
    simpa [prefixWord, tailWord_1357858, baseEnd_1357858] using wordTrace_append hprefix tailTrace_1357858
  have hstable : (prefixWord ++ tailWord_1357858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357858).length < 2 ^ (prefixWord ++ tailWord_1357858).sum := by decide
  have hdescent : baseEnd_1357858 < baseStart_1357858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357903 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 5]
def baseStart_1357903 : Nat := 118140960795 + 1357903 * 2 ^ 59
def prefixEnd_1357903 : Nat := 4983230072969 + 3 ^ 40 * 1357903 * 2
def baseEnd_1357903 : Nat := 154945982484956873770583

theorem tailTrace_1357903 : CollatzResearch.WordTrace tailWord_1357903 prefixEnd_1357903 154945982484956873770583 := by
  unfold tailWord_1357903
  simp only [CollatzResearch.WordTrace]
  refine ⟨49526791199556817214102363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33017860799704544809401575 49526791199556817214102363)
  ·
    refine ⟨74290186799335225821153545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49526791199556817214102363 74290186799335225821153545)
    ·
      refine ⟨55717640099501419365865159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74290186799335225821153545 55717640099501419365865159)
      ·
        refine ⟨83576460149252129048797739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55717640099501419365865159 83576460149252129048797739)
        ·
          refine ⟨125364690223878193573196609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83576460149252129048797739 125364690223878193573196609)
          ·
            refine ⟨94023517667908645179897457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125364690223878193573196609 94023517667908645179897457)
            ·
              refine ⟨70517638250931483884923093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94023517667908645179897457 70517638250931483884923093)
              ·
                refine ⟨1652757146506206653552885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70517638250931483884923093 1652757146506206653552885)
                ·
                  refine ⟨154945982484956873770583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1652757146506206653552885 154945982484956873770583)
                  ·
                    rfl

theorem cell22_1357903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].length) (baseStart_1357903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357903 prefixEnd_1357903 := by exact prefixLift 1357903
  have htrace : WordTrace (prefixWord ++ tailWord_1357903) baseStart_1357903 baseEnd_1357903 := by
    simpa [prefixWord, tailWord_1357903, baseEnd_1357903] using wordTrace_append hprefix tailTrace_1357903
  have hstable : (prefixWord ++ tailWord_1357903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357903).length < 2 ^ (prefixWord ++ tailWord_1357903).sum := by decide
  have hdescent : baseEnd_1357903 < baseStart_1357903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357980 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1357980 : Nat := 118140960795 + 1357980 * 2 ^ 59
def prefixEnd_1357980 : Nat := 4983230072969 + 3 ^ 40 * 1357980 * 2
def baseEnd_1357980 : Nat := 464864306128468087136513

theorem tailTrace_1357980 : CollatzResearch.WordTrace tailWord_1357980 prefixEnd_1357980 464864306128468087136513 := by
  unfold tailWord_1357980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24764799810138929682327697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33019733080185239576436929 24764799810138929682327697)
  ·
    refine ⟨18573599857604197261745773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24764799810138929682327697 18573599857604197261745773)
    ·
      refine ⟨6965099946601573973154665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18573599857604197261745773 6965099946601573973154665)
      ·
        refine ⟨5223824959951180479865999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6965099946601573973154665 5223824959951180479865999)
        ·
          refine ⟨7835737439926770719798999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223824959951180479865999 7835737439926770719798999)
          ·
            refine ⟨11753606159890156079698499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835737439926770719798999 11753606159890156079698499)
            ·
              refine ⟨17630409239835234119547749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11753606159890156079698499 17630409239835234119547749)
              ·
                refine ⟨3305701732469106397415203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17630409239835234119547749 3305701732469106397415203)
                ·
                  refine ⟨4958552598703659596122805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305701732469106397415203 4958552598703659596122805)
                  ·
                    refine ⟨464864306128468087136513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4958552598703659596122805 464864306128468087136513)
                    ·
                      rfl

theorem cell22_1357980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1357980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357980 prefixEnd_1357980 := by exact prefixLift 1357980
  have htrace : WordTrace (prefixWord ++ tailWord_1357980) baseStart_1357980 baseEnd_1357980 := by
    simpa [prefixWord, tailWord_1357980, baseEnd_1357980] using wordTrace_append hprefix tailTrace_1357980
  have hstable : (prefixWord ++ tailWord_1357980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357980).length < 2 ^ (prefixWord ++ tailWord_1357980).sum := by decide
  have hdescent : baseEnd_1357980 < baseStart_1357980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357984 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_1357984 : Nat := 118140960795 + 1357984 * 2 ^ 59
def prefixEnd_1357984 : Nat := 4983230072969 + 3 ^ 40 * 1357984 * 2
def baseEnd_1357984 : Nat := 464865675410213410036501

theorem tailTrace_1357984 : CollatzResearch.WordTrace tailWord_1357984 prefixEnd_1357984 464865675410213410036501 := by
  unfold tailWord_1357984
  simp only [CollatzResearch.WordTrace]
  refine ⟨24764872756131684023900503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33019830341508912031867337 24764872756131684023900503)
  ·
    refine ⟨37147309134197526035850755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24764872756131684023900503 37147309134197526035850755)
    ·
      refine ⟨55720963701296289053776133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37147309134197526035850755 55720963701296289053776133)
      ·
        refine ⟨10447680693993054197583025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55720963701296289053776133 10447680693993054197583025)
        ·
          refine ⟨7835760520494790648187269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447680693993054197583025 7835760520494790648187269)
          ·
            refine ⟨1469205097592773246535113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7835760520494790648187269 1469205097592773246535113)
            ·
              refine ⟨1101903823194579934901335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469205097592773246535113 1101903823194579934901335)
              ·
                refine ⟨1652855734791869902352003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101903823194579934901335 1652855734791869902352003)
                ·
                  refine ⟨2479283602187804853528005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652855734791869902352003 2479283602187804853528005)
                  ·
                    refine ⟨464865675410213410036501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479283602187804853528005 464865675410213410036501)
                    ·
                      rfl

theorem cell22_1357984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_1357984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1357984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1357984 prefixEnd_1357984 := by exact prefixLift 1357984
  have htrace : WordTrace (prefixWord ++ tailWord_1357984) baseStart_1357984 baseEnd_1357984 := by
    simpa [prefixWord, tailWord_1357984, baseEnd_1357984] using wordTrace_append hprefix tailTrace_1357984
  have hstable : (prefixWord ++ tailWord_1357984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357984).length < 2 ^ (prefixWord ++ tailWord_1357984).sum := by decide
  have hdescent : baseEnd_1357984 < baseStart_1357984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358014 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1358014 : Nat := 118140960795 + 1358014 * 2 ^ 59
def prefixEnd_1358014 : Nat := 4983230072969 + 3 ^ 40 * 1358014 * 2
def baseEnd_1358014 : Nat := 464875945023303331786409

theorem tailTrace_1358014 : CollatzResearch.WordTrace tailWord_1358014 prefixEnd_1358014 464875945023303331786409 := by
  unfold tailWord_1358014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191354962769335396424137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33020559801436455447595397 6191354962769335396424137)
  ·
    refine ⟨4643516222077001547318103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6191354962769335396424137 4643516222077001547318103)
    ·
      refine ⟨6965274333115502320977155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643516222077001547318103 6965274333115502320977155)
      ·
        refine ⟨10447911499673253481465733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965274333115502320977155 10447911499673253481465733)
        ·
          refine ⟨1958983406188735027774825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10447911499673253481465733 1958983406188735027774825)
          ·
            refine ⟨1469237554641551270831119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958983406188735027774825 1469237554641551270831119)
            ·
              refine ⟨2203856331962326906246679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469237554641551270831119 2203856331962326906246679)
              ·
                refine ⟨3305784497943490359370019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203856331962326906246679 3305784497943490359370019)
                ·
                  refine ⟨4958676746915235539055029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305784497943490359370019 4958676746915235539055029)
                  ·
                    refine ⟨464875945023303331786409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4958676746915235539055029 464875945023303331786409)
                    ·
                      rfl

theorem cell22_1358014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1358014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358014 prefixEnd_1358014 := by exact prefixLift 1358014
  have htrace : WordTrace (prefixWord ++ tailWord_1358014) baseStart_1358014 baseEnd_1358014 := by
    simpa [prefixWord, tailWord_1358014, baseEnd_1358014] using wordTrace_append hprefix tailTrace_1358014
  have hstable : (prefixWord ++ tailWord_1358014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358014).length < 2 ^ (prefixWord ++ tailWord_1358014).sum := by decide
  have hdescent : baseEnd_1358014 < baseStart_1358014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358025 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_1358025 : Nat := 118140960795 + 1358025 * 2 ^ 59
def prefixEnd_1358025 : Nat := 4983230072969 + 3 ^ 40 * 1358025 * 2
def baseEnd_1358025 : Nat := 464879710548102969761375

theorem tailTrace_1358025 : CollatzResearch.WordTrace tailWord_1358025 prefixEnd_1358025 464879710548102969761375 := by
  unfold tailWord_1358025
  simp only [CollatzResearch.WordTrace]
  refine ⟨49531240905114832050043529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33020827270076554700029019 49531240905114832050043529)
  ·
    refine ⟨37148430678836124037532647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49531240905114832050043529 37148430678836124037532647)
    ·
      refine ⟨55722646018254186056298971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37148430678836124037532647 55722646018254186056298971)
      ·
        refine ⟨83583969027381279084448457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55722646018254186056298971 83583969027381279084448457)
        ·
          refine ⟨62687976770535959313336343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83583969027381279084448457 62687976770535959313336343)
          ·
            refine ⟨94031965155803938970004515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62687976770535959313336343 94031965155803938970004515)
            ·
              refine ⟨141047947733705908455006773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94031965155803938970004515 141047947733705908455006773)
              ·
                refine ⟨13223245100034928917656885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141047947733705908455006773 13223245100034928917656885)
                ·
                  refine ⟨1239679228128274586030333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13223245100034928917656885 1239679228128274586030333)
                  ·
                    refine ⟨464879710548102969761375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239679228128274586030333 464879710548102969761375)
                    ·
                      rfl

theorem cell22_1358025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_1358025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358025 prefixEnd_1358025 := by exact prefixLift 1358025
  have htrace : WordTrace (prefixWord ++ tailWord_1358025) baseStart_1358025 baseEnd_1358025 := by
    simpa [prefixWord, tailWord_1358025, baseEnd_1358025] using wordTrace_append hprefix tailTrace_1358025
  have hstable : (prefixWord ++ tailWord_1358025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358025).length < 2 ^ (prefixWord ++ tailWord_1358025).sum := by decide
  have hdescent : baseEnd_1358025 < baseStart_1358025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358044 : List Nat := [2, 2, 5, 2, 1, 2, 8]
def baseStart_1358044 : Nat := 118140960795 + 1358044 * 2 ^ 59
def prefixEnd_1358044 : Nat := 4983230072969 + 3 ^ 40 * 1358044 * 2
def baseEnd_1358044 : Nat := 17218007949496046427271

theorem tailTrace_1358044 : CollatzResearch.WordTrace tailWord_1358044 prefixEnd_1358044 17218007949496046427271 := by
  unfold tailWord_1358044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24765966946022999147492593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33021289261363998863323457 24765966946022999147492593)
  ·
    refine ⟨18574475209517249360619445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24765966946022999147492593 18574475209517249360619445)
    ·
      refine ⟨1741357050892242127558073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18574475209517249360619445 1741357050892242127558073)
      ·
        refine ⟨1306017788169181595668555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741357050892242127558073 1306017788169181595668555)
        ·
          refine ⟨1959026682253772393502833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306017788169181595668555 1959026682253772393502833)
          ·
            refine ⟨1469270011690329295127125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959026682253772393502833 1469270011690329295127125)
            ·
              refine ⟨17218007949496046427271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1469270011690329295127125 17218007949496046427271)
              ·
                rfl

theorem cell22_1358044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 8].length) (baseStart_1358044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358044 prefixEnd_1358044 := by exact prefixLift 1358044
  have htrace : WordTrace (prefixWord ++ tailWord_1358044) baseStart_1358044 baseEnd_1358044 := by
    simpa [prefixWord, tailWord_1358044, baseEnd_1358044] using wordTrace_append hprefix tailTrace_1358044
  have hstable : (prefixWord ++ tailWord_1358044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358044).length < 2 ^ (prefixWord ++ tailWord_1358044).sum := by decide
  have hdescent : baseEnd_1358044 < baseStart_1358044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358050 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1358050 : Nat := 118140960795 + 1358050 * 2 ^ 59
def prefixEnd_1358050 : Nat := 4983230072969 + 3 ^ 40 * 1358050 * 2
def baseEnd_1358050 : Nat := 154962756186337079295433

theorem tailTrace_1358050 : CollatzResearch.WordTrace tailWord_1358050 prefixEnd_1358050 154962756186337079295433 := by
  unfold tailWord_1358050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383038182506065329925901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33021435153349507546469069 12383038182506065329925901)
  ·
    refine ⟨4643639318439774498722213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12383038182506065329925901 4643639318439774498722213)
    ·
      refine ⟨870682372207457718510415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4643639318439774498722213 870682372207457718510415)
      ·
        refine ⟨1306023558311186577765623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870682372207457718510415 1306023558311186577765623)
        ·
          refine ⟨1959035337466779866648435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306023558311186577765623 1959035337466779866648435)
          ·
            refine ⟨2938553006200169799972653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959035337466779866648435 2938553006200169799972653)
            ·
              refine ⟨1101957377325063674989745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2938553006200169799972653 1101957377325063674989745)
              ·
                refine ⟨826468032993797756242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101957377325063674989745 826468032993797756242309)
                ·
                  refine ⟨154962756186337079295433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 826468032993797756242309 154962756186337079295433)
                  ·
                    rfl

theorem cell22_1358050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1358050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358050 prefixEnd_1358050 := by exact prefixLift 1358050
  have htrace : WordTrace (prefixWord ++ tailWord_1358050) baseStart_1358050 baseEnd_1358050 := by
    simpa [prefixWord, tailWord_1358050, baseEnd_1358050] using wordTrace_append hprefix tailTrace_1358050
  have hstable : (prefixWord ++ tailWord_1358050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358050).length < 2 ^ (prefixWord ++ tailWord_1358050).sum := by decide
  have hdescent : baseEnd_1358050 < baseStart_1358050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358110 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1358110 : Nat := 118140960795 + 1358110 * 2 ^ 59
def prefixEnd_1358110 : Nat := 4983230072969 + 3 ^ 40 * 1358110 * 2
def baseEnd_1358110 : Nat := 464908807785191081386115

theorem tailTrace_1358110 : CollatzResearch.WordTrace tailWord_1358110 prefixEnd_1358110 464908807785191081386115 := by
  unfold tailWord_1358110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191792638725861445860973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33022894073204594377925189 6191792638725861445860973)
  ·
    refine ⟨2321922239522198042197865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6191792638725861445860973 2321922239522198042197865)
    ·
      refine ⟨1741441679641648531648399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321922239522198042197865 1741441679641648531648399)
      ·
        refine ⟨2612162519462472797472599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741441679641648531648399 2612162519462472797472599)
        ·
          refine ⟨3918243779193709196208899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612162519462472797472599 3918243779193709196208899)
          ·
            refine ⟨5877365668790563794313349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918243779193709196208899 5877365668790563794313349)
            ·
              refine ⟨1102006062898230711433753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5877365668790563794313349 1102006062898230711433753)
              ·
                refine ⟨826504547173673033575315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102006062898230711433753 826504547173673033575315)
                ·
                  refine ⟨1239756820760509550362973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826504547173673033575315 1239756820760509550362973)
                  ·
                    refine ⟨464908807785191081386115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239756820760509550362973 464908807785191081386115)
                    ·
                      rfl

theorem cell22_1358110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1358110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358110 prefixEnd_1358110 := by exact prefixLift 1358110
  have htrace : WordTrace (prefixWord ++ tailWord_1358110) baseStart_1358110 baseEnd_1358110 := by
    simpa [prefixWord, tailWord_1358110, baseEnd_1358110] using wordTrace_append hprefix tailTrace_1358110
  have hstable : (prefixWord ++ tailWord_1358110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358110).length < 2 ^ (prefixWord ++ tailWord_1358110).sum := by decide
  have hdescent : baseEnd_1358110 < baseStart_1358110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358115 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_1358115 : Nat := 118140960795 + 1358115 * 2 ^ 59
def prefixEnd_1358115 : Nat := 4983230072969 + 3 ^ 40 * 1358115 * 2
def baseEnd_1358115 : Nat := 464910519387372735011099

theorem tailTrace_1358115 : CollatzResearch.WordTrace tailWord_1358115 prefixEnd_1358115 464910519387372735011099 := by
  unfold tailWord_1358115
  simp only [CollatzResearch.WordTrace]
  refine ⟨49534523474788777420819799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33023015649859184947213199 49534523474788777420819799)
  ·
    refine ⟨74301785212183166131229699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49534523474788777420819799 74301785212183166131229699)
    ·
      refine ⟨111452677818274749196844549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74301785212183166131229699 111452677818274749196844549)
      ·
        refine ⟨20897377090926515474408353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111452677818274749196844549 20897377090926515474408353)
        ·
          refine ⟨15673032818194886605806265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20897377090926515474408353 15673032818194886605806265)
          ·
            refine ⟨11754774613646164954354699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15673032818194886605806265 11754774613646164954354699)
            ·
              refine ⟨17632161920469247431532049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11754774613646164954354699 17632161920469247431532049)
              ·
                refine ⟨13224121440351935573649037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17632161920469247431532049 13224121440351935573649037)
                ·
                  refine ⟨4959045540131975840118389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13224121440351935573649037 4959045540131975840118389)
                  ·
                    refine ⟨464910519387372735011099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4959045540131975840118389 464910519387372735011099)
                    ·
                      rfl

theorem cell22_1358115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_1358115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358115 prefixEnd_1358115 := by exact prefixLift 1358115
  have htrace : WordTrace (prefixWord ++ tailWord_1358115) baseStart_1358115 baseEnd_1358115 := by
    simpa [prefixWord, tailWord_1358115, baseEnd_1358115] using wordTrace_append hprefix tailTrace_1358115
  have hstable : (prefixWord ++ tailWord_1358115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358115).length < 2 ^ (prefixWord ++ tailWord_1358115).sum := by decide
  have hdescent : baseEnd_1358115 < baseStart_1358115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358147 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_1358147 : Nat := 118140960795 + 1358147 * 2 ^ 59
def prefixEnd_1358147 : Nat := 4983230072969 + 3 ^ 40 * 1358147 * 2
def baseEnd_1358147 : Nat := 464921473641335318211001

theorem tailTrace_1358147 : CollatzResearch.WordTrace tailWord_1358147 prefixEnd_1358147 464921473641335318211001 := by
  unfold tailWord_1358147
  simp only [CollatzResearch.WordTrace]
  refine ⟨49535690610672846885984695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33023793740448564590656463 49535690610672846885984695)
  ·
    refine ⟨74303535916009270328977043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49535690610672846885984695 74303535916009270328977043)
    ·
      refine ⟨111455303874013905493465565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74303535916009270328977043 111455303874013905493465565)
      ·
        refine ⟨41795738952755214560049587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111455303874013905493465565 41795738952755214560049587)
        ·
          refine ⟨62693608429132821840074381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41795738952755214560049587 62693608429132821840074381)
          ·
            refine ⟨23510103160924808190027893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62693608429132821840074381 23510103160924808190027893)
            ·
              refine ⟨2204072171336700767815115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23510103160924808190027893 2204072171336700767815115)
              ·
                refine ⟨3306108257005051151722673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204072171336700767815115 3306108257005051151722673)
                ·
                  refine ⟨2479581192753788363792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306108257005051151722673 2479581192753788363792005)
                  ·
                    refine ⟨464921473641335318211001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2479581192753788363792005 464921473641335318211001)
                    ·
                      rfl

theorem cell22_1358147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_1358147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1358147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1358147 prefixEnd_1358147 := by exact prefixLift 1358147
  have htrace : WordTrace (prefixWord ++ tailWord_1358147) baseStart_1358147 baseEnd_1358147 := by
    simpa [prefixWord, tailWord_1358147, baseEnd_1358147] using wordTrace_append hprefix tailTrace_1358147
  have hstable : (prefixWord ++ tailWord_1358147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358147).length < 2 ^ (prefixWord ++ tailWord_1358147).sum := by decide
  have hdescent : baseEnd_1358147 < baseStart_1358147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
