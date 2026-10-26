import V185TrunkScan23Chunk1264

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7493843 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_7493843 : Nat := 118140960795 + 7493843 * 2 ^ 59
def prefixEnd_7493843 : Nat := 4983230072969 + 3 ^ 40 * 7493843 * 2
def baseEnd_7493843 : Nat := 3847943408331029038498949

theorem tailTrace_7493843 : CollatzResearch.WordTrace tailWord_7493843 prefixEnd_7493843 3847943408331029038498949 := by
  unfold tailWord_7493843
  simp only [CollatzResearch.WordTrace]
  refine ⟨273322908590094132335726183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182215272393396088223817455 273322908590094132335726183)
  ·
    refine ⟨409984362885141198503589275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273322908590094132335726183 409984362885141198503589275)
    ·
      refine ⟨614976544327711797755383913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409984362885141198503589275 614976544327711797755383913)
      ·
        refine ⟨461232408245783848316537935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614976544327711797755383913 461232408245783848316537935)
        ·
          refine ⟨691848612368675772474806903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461232408245783848316537935 691848612368675772474806903)
          ·
            refine ⟨1037772918553013658712210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691848612368675772474806903 1037772918553013658712210355)
            ·
              refine ⟨1556659377829520488068315533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037772918553013658712210355 1556659377829520488068315533)
              ·
                refine ⟨583747266686070183025618325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556659377829520488068315533 583747266686070183025618325)
                ·
                  refine ⟨27363153125909539829325859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 583747266686070183025618325 27363153125909539829325859)
                  ·
                    refine ⟨41044729688864309743988789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27363153125909539829325859 41044729688864309743988789)
                    ·
                      refine ⟨3847943408331029038498949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41044729688864309743988789 3847943408331029038498949)
                      ·
                        rfl

theorem cell23_7493843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_7493843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493843 prefixEnd_7493843 := by exact prefixLift 7493843
  have htrace : WordTrace (prefixWord ++ tailWord_7493843) baseStart_7493843 baseEnd_7493843 := by
    simpa [prefixWord, tailWord_7493843, baseEnd_7493843] using wordTrace_append hprefix tailTrace_7493843
  have hstable : (prefixWord ++ tailWord_7493843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493843).length < 2 ^ (prefixWord ++ tailWord_7493843).sum := by decide
  have hdescent : baseEnd_7493843 < baseStart_7493843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493857 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_7493857 : Nat := 118140960795 + 7493857 * 2 ^ 59
def prefixEnd_7493857 : Nat := 4983230072969 + 3 ^ 40 * 7493857 * 2
def baseEnd_7493857 : Nat := 3847950597060191983723885

theorem tailTrace_7493857 : CollatzResearch.WordTrace tailWord_7493857 prefixEnd_7493857 3847950597060191983723885 := by
  unfold tailWord_7493857
  simp only [CollatzResearch.WordTrace]
  refine ⟨273323419212043412726735825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182215612808028941817823883 273323419212043412726735825)
  ·
    refine ⟨204992564409032559545051869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273323419212043412726735825 204992564409032559545051869)
    ·
      refine ⟨76872211653387209829394451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204992564409032559545051869 76872211653387209829394451)
      ·
        refine ⟨115308317480080814744091677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76872211653387209829394451 115308317480080814744091677)
        ·
          refine ⟨43240619055030305529034379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115308317480080814744091677 43240619055030305529034379)
          ·
            refine ⟨64860928582545458293551569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43240619055030305529034379 64860928582545458293551569)
            ·
              refine ⟨48645696436909093720163677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64860928582545458293551569 48645696436909093720163677)
              ·
                refine ⟨18242136163840910145061379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48645696436909093720163677 18242136163840910145061379)
                ·
                  refine ⟨27363204245761365217592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18242136163840910145061379 27363204245761365217592069)
                  ·
                    refine ⟨5130600796080255978298513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27363204245761365217592069 5130600796080255978298513)
                    ·
                      refine ⟨3847950597060191983723885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130600796080255978298513 3847950597060191983723885)
                      ·
                        rfl

theorem cell23_7493857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_7493857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493857 prefixEnd_7493857 := by exact prefixLift 7493857
  have htrace : WordTrace (prefixWord ++ tailWord_7493857) baseStart_7493857 baseEnd_7493857 := by
    simpa [prefixWord, tailWord_7493857, baseEnd_7493857] using wordTrace_append hprefix tailTrace_7493857
  have hstable : (prefixWord ++ tailWord_7493857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493857).length < 2 ^ (prefixWord ++ tailWord_7493857).sum := by decide
  have hdescent : baseEnd_7493857 < baseStart_7493857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493861 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7493861 : Nat := 118140960795 + 7493861 * 2 ^ 59
def prefixEnd_7493861 : Nat := 4983230072969 + 3 ^ 40 * 7493861 * 2
def baseEnd_7493861 : Nat := 3847952650982809968073867

theorem tailTrace_7493861 : CollatzResearch.WordTrace tailWord_7493861 prefixEnd_7493861 3847952650982809968073867 := by
  unfold tailWord_7493861
  simp only [CollatzResearch.WordTrace]
  refine ⟨273323565104028921409881437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182215710069352614273254291 273323565104028921409881437)
  ·
    refine ⟨102496336914010845528705539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273323565104028921409881437 102496336914010845528705539)
    ·
      refine ⟨153744505371016268293058309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102496336914010845528705539 153744505371016268293058309)
      ·
        refine ⟨28827094757065550304948433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153744505371016268293058309 28827094757065550304948433)
        ·
          refine ⟨21620321067799162728711325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28827094757065550304948433 21620321067799162728711325)
          ·
            refine ⟨8107620400424686023266747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21620321067799162728711325 8107620400424686023266747)
            ·
              refine ⟨12161430600637029034900121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107620400424686023266747 12161430600637029034900121)
              ·
                refine ⟨9121072950477771776175091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12161430600637029034900121 9121072950477771776175091)
                ·
                  refine ⟨13681609425716657664262637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121072950477771776175091 13681609425716657664262637)
                  ·
                    refine ⟨5130603534643746624098489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13681609425716657664262637 5130603534643746624098489)
                    ·
                      refine ⟨3847952650982809968073867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130603534643746624098489 3847952650982809968073867)
                      ·
                        rfl

theorem cell23_7493861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7493861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493861 prefixEnd_7493861 := by exact prefixLift 7493861
  have htrace : WordTrace (prefixWord ++ tailWord_7493861) baseStart_7493861 baseEnd_7493861 := by
    simpa [prefixWord, tailWord_7493861, baseEnd_7493861] using wordTrace_append hprefix tailTrace_7493861
  have hstable : (prefixWord ++ tailWord_7493861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493861).length < 2 ^ (prefixWord ++ tailWord_7493861).sum := by decide
  have hdescent : baseEnd_7493861 < baseStart_7493861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493870 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7493870 : Nat := 118140960795 + 7493870 * 2 ^ 59
def prefixEnd_7493870 : Nat := 4983230072969 + 3 ^ 40 * 7493870 * 2
def baseEnd_7493870 : Nat := 3847957272308700432861325

theorem tailTrace_7493870 : CollatzResearch.WordTrace tailWord_7493870 prefixEnd_7493870 3847957272308700432861325 := by
  unfold tailWord_7493870
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165486670124539493369883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182215928907330877297972709 34165486670124539493369883)
  ·
    refine ⟨51248230005186809240054825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34165486670124539493369883 51248230005186809240054825)
    ·
      refine ⟨38436172503890106930041119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51248230005186809240054825 38436172503890106930041119)
      ·
        refine ⟨57654258755835160395061679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38436172503890106930041119 57654258755835160395061679)
        ·
          refine ⟨86481388133752740592592519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57654258755835160395061679 86481388133752740592592519)
          ·
            refine ⟨129722082200629110888888779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86481388133752740592592519 129722082200629110888888779)
            ·
              refine ⟨194583123300943666333333169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129722082200629110888888779 194583123300943666333333169)
              ·
                refine ⟨145937342475707749749999877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194583123300943666333333169 145937342475707749749999877)
                ·
                  refine ⟨27363251714195203078124977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145937342475707749749999877 27363251714195203078124977)
                  ·
                    refine ⟨20522438785646402308593733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27363251714195203078124977 20522438785646402308593733)
                    ·
                      refine ⟨3847957272308700432861325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20522438785646402308593733 3847957272308700432861325)
                      ·
                        rfl

theorem cell23_7493870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7493870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493870 prefixEnd_7493870 := by exact prefixLift 7493870
  have htrace : WordTrace (prefixWord ++ tailWord_7493870) baseStart_7493870 baseEnd_7493870 := by
    simpa [prefixWord, tailWord_7493870, baseEnd_7493870] using wordTrace_append hprefix tailTrace_7493870
  have hstable : (prefixWord ++ tailWord_7493870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493870).length < 2 ^ (prefixWord ++ tailWord_7493870).sum := by decide
  have hdescent : baseEnd_7493870 < baseStart_7493870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493874 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7493874 : Nat := 118140960795 + 7493874 * 2 ^ 59
def prefixEnd_7493874 : Nat := 4983230072969 + 3 ^ 40 * 7493874 * 2
def baseEnd_7493874 : Nat := 3847959326231318417211307

theorem tailTrace_7493874 : CollatzResearch.WordTrace tailWord_7493874 prefixEnd_7493874 3847959326231318417211307 := by
  unfold tailWord_7493874
  simp only [CollatzResearch.WordTrace]
  refine ⟨68331009813245456157526169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182216026168654549753403117 68331009813245456157526169)
  ·
    refine ⟨51248257359934092118144627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68331009813245456157526169 51248257359934092118144627)
    ·
      refine ⟨76872386039901138177216941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51248257359934092118144627 76872386039901138177216941)
      ·
        refine ⟨28827144764962926816456353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76872386039901138177216941 28827144764962926816456353)
        ·
          refine ⟨21620358573722195112342265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28827144764962926816456353 21620358573722195112342265)
          ·
            refine ⟨16215268930291646334256699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21620358573722195112342265 16215268930291646334256699)
            ·
              refine ⟨24322903395437469501385049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16215268930291646334256699 24322903395437469501385049)
              ·
                refine ⟨18242177546578102126038787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24322903395437469501385049 18242177546578102126038787)
                ·
                  refine ⟨27363266319867153189058181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18242177546578102126038787 27363266319867153189058181)
                  ·
                    refine ⟨5130612434975091222948409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27363266319867153189058181 5130612434975091222948409)
                    ·
                      refine ⟨3847959326231318417211307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130612434975091222948409 3847959326231318417211307)
                      ·
                        rfl

theorem cell23_7493874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7493874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493874 prefixEnd_7493874 := by exact prefixLift 7493874
  have htrace : WordTrace (prefixWord ++ tailWord_7493874) baseStart_7493874 baseEnd_7493874 := by
    simpa [prefixWord, tailWord_7493874, baseEnd_7493874] using wordTrace_append hprefix tailTrace_7493874
  have hstable : (prefixWord ++ tailWord_7493874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493874).length < 2 ^ (prefixWord ++ tailWord_7493874).sum := by decide
  have hdescent : baseEnd_7493874 < baseStart_7493874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493897 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 5]
def baseStart_7493897 : Nat := 118140960795 + 7493897 * 2 ^ 59
def prefixEnd_7493897 : Nat := 4983230072969 + 3 ^ 40 * 7493897 * 2
def baseEnd_7493897 : Nat := 427552348476263536358189

theorem tailTrace_7493897 : CollatzResearch.WordTrace tailWord_7493897 prefixEnd_7493897 427552348476263536358189 := by
  unfold tailWord_7493897
  simp only [CollatzResearch.WordTrace]
  refine ⟨273324878131898499558191945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182216585421265666372127963 273324878131898499558191945)
  ·
    refine ⟨204993658598923874668643959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273324878131898499558191945 204993658598923874668643959)
    ·
      refine ⟨307490487898385812002965939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204993658598923874668643959 307490487898385812002965939)
      ·
        refine ⟨461235731847578718004448909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307490487898385812002965939 461235731847578718004448909)
        ·
          refine ⟨172963399442842019251668341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461235731847578718004448909 172963399442842019251668341)
          ·
            refine ⟨16215318697766439304843907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172963399442842019251668341 16215318697766439304843907)
            ·
              refine ⟨24322978046649658957265861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16215318697766439304843907 24322978046649658957265861)
              ·
                refine ⟨4560558383746811054487349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24322978046649658957265861 4560558383746811054487349)
                ·
                  refine ⟨427552348476263536358189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560558383746811054487349 427552348476263536358189)
                  ·
                    rfl

theorem cell23_7493897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 5].length) (baseStart_7493897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493897 prefixEnd_7493897 := by exact prefixLift 7493897
  have htrace : WordTrace (prefixWord ++ tailWord_7493897) baseStart_7493897 baseEnd_7493897 := by
    simpa [prefixWord, tailWord_7493897, baseEnd_7493897] using wordTrace_append hprefix tailTrace_7493897
  have hstable : (prefixWord ++ tailWord_7493897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493897).length < 2 ^ (prefixWord ++ tailWord_7493897).sum := by decide
  have hdescent : baseEnd_7493897 < baseStart_7493897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493982 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_7493982 : Nat := 118140960795 + 7493982 * 2 ^ 59
def prefixEnd_7493982 : Nat := 4983230072969 + 3 ^ 40 * 7493982 * 2
def baseEnd_7493982 : Nat := 427557198015778221628979

theorem tailTrace_7493982 : CollatzResearch.WordTrace tailWord_7493982 prefixEnd_7493982 427557198015778221628979 := by
  unfold tailWord_7493982
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165997292073819884379525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182218652224393706050024133 34165997292073819884379525)
  ·
    refine ⟨6406124492263841228321161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34165997292073819884379525 6406124492263841228321161)
    ·
      refine ⟨4804593369197880921240871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6406124492263841228321161 4804593369197880921240871)
      ·
        refine ⟨7206890053796821381861307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804593369197880921240871 7206890053796821381861307)
        ·
          refine ⟨10810335080695232072791961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206890053796821381861307 10810335080695232072791961)
          ·
            refine ⟨8107751310521424054593971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810335080695232072791961 8107751310521424054593971)
            ·
              refine ⟨12161626965782136081890957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107751310521424054593971 12161626965782136081890957)
              ·
                refine ⟨4560610112168301030709109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12161626965782136081890957 4560610112168301030709109)
                ·
                  refine ⟨427557198015778221628979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560610112168301030709109 427557198015778221628979)
                  ·
                    rfl

theorem cell23_7493982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_7493982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493982 prefixEnd_7493982 := by exact prefixLift 7493982
  have htrace : WordTrace (prefixWord ++ tailWord_7493982) baseStart_7493982 baseEnd_7493982 := by
    simpa [prefixWord, tailWord_7493982, baseEnd_7493982] using wordTrace_append hprefix tailTrace_7493982
  have hstable : (prefixWord ++ tailWord_7493982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493982).length < 2 ^ (prefixWord ++ tailWord_7493982).sum := by decide
  have hdescent : baseEnd_7493982 < baseStart_7493982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7493991 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 1, 4]
def baseStart_7493991 : Nat := 118140960795 + 7493991 * 2 ^ 59
def prefixEnd_7493991 : Nat := 4983230072969 + 3 ^ 40 * 7493991 * 2
def baseEnd_7493991 : Nat := 1282673134489298153149423

theorem tailTrace_7493991 : CollatzResearch.WordTrace tailWord_7493991 prefixEnd_7493991 1282673134489298153149423 := by
  unfold tailWord_7493991
  simp only [CollatzResearch.WordTrace]
  refine ⟨273328306593557953612113827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182218871062371969074742551 273328306593557953612113827)
  ·
    refine ⟨409992459890336930418170741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273328306593557953612113827 409992459890336930418170741)
    ·
      refine ⟨38436793114719087226703507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 409992459890336930418170741 38436793114719087226703507)
      ·
        refine ⟨57655189672078630840055261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38436793114719087226703507 57655189672078630840055261)
        ·
          refine ⟨21620696127029486565020723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57655189672078630840055261 21620696127029486565020723)
          ·
            refine ⟨32431044190544229847531085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21620696127029486565020723 32431044190544229847531085)
            ·
              refine ⟨12161641571454086192824157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32431044190544229847531085 12161641571454086192824157)
              ·
                refine ⟨4560615589295282322309059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12161641571454086192824157 4560615589295282322309059)
                ·
                  refine ⟨6840923383942923483463589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560615589295282322309059 6840923383942923483463589)
                  ·
                    refine ⟨1282673134489298153149423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6840923383942923483463589 1282673134489298153149423)
                    ·
                      rfl

theorem cell23_7493991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_7493991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7493991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7493991 prefixEnd_7493991 := by exact prefixLift 7493991
  have htrace : WordTrace (prefixWord ++ tailWord_7493991) baseStart_7493991 baseEnd_7493991 := by
    simpa [prefixWord, tailWord_7493991, baseEnd_7493991] using wordTrace_append hprefix tailTrace_7493991
  have hstable : (prefixWord ++ tailWord_7493991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7493991).length < 2 ^ (prefixWord ++ tailWord_7493991).sum := by decide
  have hdescent : baseEnd_7493991 < baseStart_7493991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7493991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494007 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_7494007 : Nat := 118140960795 + 7494007 * 2 ^ 59
def prefixEnd_7494007 : Nat := 4983230072969 + 3 ^ 40 * 7494007 * 2
def baseEnd_7494007 : Nat := 3848027619158366396848195

theorem tailTrace_7494007 : CollatzResearch.WordTrace tailWord_7494007 prefixEnd_7494007 3848027619158366396848195 := by
  unfold tailWord_7494007
  simp only [CollatzResearch.WordTrace]
  refine ⟨273328890161499988344696275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182219260107666658896464183 273328890161499988344696275)
  ·
    refine ⟨409993335242249982517044413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273328890161499988344696275 409993335242249982517044413)
    ·
      refine ⟨153747500715843743443891655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409993335242249982517044413 153747500715843743443891655)
      ·
        refine ⟨230621251073765615165837483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153747500715843743443891655 230621251073765615165837483)
        ·
          refine ⟨345931876610648422748756225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230621251073765615165837483 345931876610648422748756225)
          ·
            refine ⟨259448907457986317061567169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345931876610648422748756225 259448907457986317061567169)
            ·
              refine ⟨194586680593489737796175377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259448907457986317061567169 194586680593489737796175377)
              ·
                refine ⟨145940010445117303347131533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194586680593489737796175377 145940010445117303347131533)
                ·
                  refine ⟨54727503916918988755174325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145940010445117303347131533 54727503916918988755174325)
                  ·
                    refine ⟨5130703492211155195797593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54727503916918988755174325 5130703492211155195797593)
                    ·
                      refine ⟨3848027619158366396848195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130703492211155195797593 3848027619158366396848195)
                      ·
                        rfl

theorem cell23_7494007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_7494007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494007 prefixEnd_7494007 := by exact prefixLift 7494007
  have htrace : WordTrace (prefixWord ++ tailWord_7494007) baseStart_7494007 baseEnd_7494007 := by
    simpa [prefixWord, tailWord_7494007, baseEnd_7494007] using wordTrace_append hprefix tailTrace_7494007
  have hstable : (prefixWord ++ tailWord_7494007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494007).length < 2 ^ (prefixWord ++ tailWord_7494007).sum := by decide
  have hdescent : baseEnd_7494007 < baseStart_7494007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494024 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7494024 : Nat := 118140960795 + 7494024 * 2 ^ 59
def prefixEnd_7494024 : Nat := 4983230072969 + 3 ^ 40 * 7494024 * 2
def baseEnd_7494024 : Nat := 3848036348329492830335617

theorem tailTrace_7494024 : CollatzResearch.WordTrace tailWord_7494024 prefixEnd_7494024 3848036348329492830335617 := by
  unfold tailWord_7494024
  simp only [CollatzResearch.WordTrace]
  refine ⟨136664755101219200124032563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182219673468292266832043417 136664755101219200124032563)
  ·
    refine ⟨204997132651828800186048845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136664755101219200124032563 204997132651828800186048845)
    ·
      refine ⟨76873924744435800069768317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204997132651828800186048845 76873924744435800069768317)
      ·
        refine ⟨28827721779163425026163119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76873924744435800069768317 28827721779163425026163119)
        ·
          refine ⟨43241582668745137539244679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28827721779163425026163119 43241582668745137539244679)
          ·
            refine ⟨64862374003117706308867019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43241582668745137539244679 64862374003117706308867019)
            ·
              refine ⟨97293561004676559463300529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64862374003117706308867019 97293561004676559463300529)
              ·
                refine ⟨72970170753507419597475397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97293561004676559463300529 72970170753507419597475397)
                ·
                  refine ⟨13681907016282641174526637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72970170753507419597475397 13681907016282641174526637)
                  ·
                    refine ⟨5130715131105990440447489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13681907016282641174526637 5130715131105990440447489)
                    ·
                      refine ⟨3848036348329492830335617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130715131105990440447489 3848036348329492830335617)
                      ·
                        rfl

theorem cell23_7494024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7494024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494024 prefixEnd_7494024 := by exact prefixLift 7494024
  have htrace : WordTrace (prefixWord ++ tailWord_7494024) baseStart_7494024 baseEnd_7494024 := by
    simpa [prefixWord, tailWord_7494024, baseEnd_7494024] using wordTrace_append hprefix tailTrace_7494024
  have hstable : (prefixWord ++ tailWord_7494024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494024).length < 2 ^ (prefixWord ++ tailWord_7494024).sum := by decide
  have hdescent : baseEnd_7494024 < baseStart_7494024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494047 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 6]
def baseStart_7494047 : Nat := 118140960795 + 7494047 * 2 ^ 59
def prefixEnd_7494047 : Nat := 4983230072969 + 3 ^ 40 * 7494047 * 2
def baseEnd_7494047 : Nat := 1282682719461515413449337

theorem tailTrace_7494047 : CollatzResearch.WordTrace tailWord_7494047 prefixEnd_7494047 1282682719461515413449337 := by
  unfold tailWord_7494047
  simp only [CollatzResearch.WordTrace]
  refine ⟨273330349081355075176152395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182220232720903383450768263 273330349081355075176152395)
  ·
    refine ⟨409995523622032612764228593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273330349081355075176152395 409995523622032612764228593)
    ·
      refine ⟨307496642716524459573171445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409995523622032612764228593 307496642716524459573171445)
      ·
        refine ⟨28827810254674168084984823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307496642716524459573171445 28827810254674168084984823)
        ·
          refine ⟨43241715382011252127477235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28827810254674168084984823 43241715382011252127477235)
          ·
            refine ⟨64862573073016878191215853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43241715382011252127477235 64862573073016878191215853)
            ·
              refine ⟨24323464902381329321705945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64862573073016878191215853 24323464902381329321705945)
              ·
                refine ⟨18242598676785996991279459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24323464902381329321705945 18242598676785996991279459)
                ·
                  refine ⟨27363898015178995486919189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18242598676785996991279459 27363898015178995486919189)
                  ·
                    refine ⟨1282682719461515413449337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27363898015178995486919189 1282682719461515413449337)
                    ·
                      rfl

theorem cell23_7494047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_7494047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494047 prefixEnd_7494047 := by exact prefixLift 7494047
  have htrace : WordTrace (prefixWord ++ tailWord_7494047) baseStart_7494047 baseEnd_7494047 := by
    simpa [prefixWord, tailWord_7494047, baseEnd_7494047] using wordTrace_append hprefix tailTrace_7494047
  have hstable : (prefixWord ++ tailWord_7494047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494047).length < 2 ^ (prefixWord ++ tailWord_7494047).sum := by decide
  have hdescent : baseEnd_7494047 < baseStart_7494047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494065 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7494065 : Nat := 118140960795 + 7494065 * 2 ^ 59
def prefixEnd_7494065 : Nat := 4983230072969 + 3 ^ 40 * 7494065 * 2
def baseEnd_7494065 : Nat := 3848057401036327169922929

theorem tailTrace_7494065 : CollatzResearch.WordTrace tailWord_7494065 prefixEnd_7494065 3848057401036327169922929 := by
  unfold tailWord_7494065
  simp only [CollatzResearch.WordTrace]
  refine ⟨273331005595289864250307649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182220670396859909500205099 273331005595289864250307649)
  ·
    refine ⟨204998254196467398187730737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273331005595289864250307649 204998254196467398187730737)
    ·
      refine ⟨153748690647350548640798053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204998254196467398187730737 153748690647350548640798053)
      ·
        refine ⟨28827879496378227870149635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153748690647350548640798053 28827879496378227870149635)
        ·
          refine ⟨43241819244567341805224453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28827879496378227870149635 43241819244567341805224453)
          ·
            refine ⟨8107841108356376588479585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43241819244567341805224453 8107841108356376588479585)
            ·
              refine ⟨6080880831267282441359689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107841108356376588479585 6080880831267282441359689)
              ·
                refine ⟨4560660623450461831019767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080880831267282441359689 4560660623450461831019767)
                ·
                  refine ⟨6840990935175692746529651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560660623450461831019767 6840990935175692746529651)
                  ·
                    refine ⟨10261486402763539119794477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6840990935175692746529651 10261486402763539119794477)
                    ·
                      refine ⟨3848057401036327169922929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261486402763539119794477 3848057401036327169922929)
                      ·
                        rfl

theorem cell23_7494065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7494065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494065 prefixEnd_7494065 := by exact prefixLift 7494065
  have htrace : WordTrace (prefixWord ++ tailWord_7494065) baseStart_7494065 baseEnd_7494065 := by
    simpa [prefixWord, tailWord_7494065, baseEnd_7494065] using wordTrace_append hprefix tailTrace_7494065
  have hstable : (prefixWord ++ tailWord_7494065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494065).length < 2 ^ (prefixWord ++ tailWord_7494065).sum := by decide
  have hdescent : baseEnd_7494065 < baseStart_7494065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494077 : List Nat := [1, 4, 1, 2, 2, 2, 3, 8]
def baseStart_7494077 : Nat := 118140960795 + 7494077 * 2 ^ 59
def prefixEnd_7494077 : Nat := 4983230072969 + 3 ^ 40 * 7494077 * 2
def baseEnd_7494077 : Nat := 142520872696451152702699

theorem tailTrace_7494077 : CollatzResearch.WordTrace tailWord_7494077 prefixEnd_7494077 142520872696451152702699 := by
  unfold tailWord_7494077
  simp only [CollatzResearch.WordTrace]
  refine ⟨273331443271246390299744485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182220962180830926866496323 273331443271246390299744485)
  ·
    refine ⟨51249645613358698181202091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273331443271246390299744485 51249645613358698181202091)
    ·
      refine ⟨76874468420038047271803137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51249645613358698181202091 76874468420038047271803137)
      ·
        refine ⟨57655851315028535453852353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76874468420038047271803137 57655851315028535453852353)
        ·
          refine ⟨43241888486271401590389265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57655851315028535453852353 43241888486271401590389265)
          ·
            refine ⟨32431416364703551192791949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43241888486271401590389265 32431416364703551192791949)
            ·
              refine ⟨12161781136763831697296981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32431416364703551192791949 12161781136763831697296981)
              ·
                refine ⟨142520872696451152702699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12161781136763831697296981 142520872696451152702699)
                ·
                  rfl

theorem cell23_7494077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 8].length) (baseStart_7494077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494077 prefixEnd_7494077 := by exact prefixLift 7494077
  have htrace : WordTrace (prefixWord ++ tailWord_7494077) baseStart_7494077 baseEnd_7494077 := by
    simpa [prefixWord, tailWord_7494077, baseEnd_7494077] using wordTrace_append hprefix tailTrace_7494077
  have hstable : (prefixWord ++ tailWord_7494077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494077).length < 2 ^ (prefixWord ++ tailWord_7494077).sum := by decide
  have hdescent : baseEnd_7494077 < baseStart_7494077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494104 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_7494104 : Nat := 118140960795 + 7494104 * 2 ^ 59
def prefixEnd_7494104 : Nat := 4983230072969 + 3 ^ 40 * 7494104 * 2
def baseEnd_7494104 : Nat := 3848077426781852517335249

theorem tailTrace_7494104 : CollatzResearch.WordTrace tailWord_7494104 prefixEnd_7494104 3848077426781852517335249 := by
  unfold tailWord_7494104
  simp only [CollatzResearch.WordTrace]
  refine ⟨136666214021074286955488683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182221618694765715940651577 136666214021074286955488683)
  ·
    refine ⟨204999321031611430433233025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136666214021074286955488683 204999321031611430433233025)
    ·
      refine ⟨153749490773708572824924769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204999321031611430433233025 153749490773708572824924769)
      ·
        refine ⟨115312118080281429618693577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153749490773708572824924769 115312118080281429618693577)
        ·
          refine ⟨86484088560211072214020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115312118080281429618693577 86484088560211072214020183)
          ·
            refine ⟨129726132840316608321030275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86484088560211072214020183 129726132840316608321030275)
            ·
              refine ⟨194589199260474912481545413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129726132840316608321030275 194589199260474912481545413)
              ·
                refine ⟨36485474861339046090289765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194589199260474912481545413 36485474861339046090289765)
                ·
                  refine ⟨6841026536501071141929331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36485474861339046090289765 6841026536501071141929331)
                  ·
                    refine ⟨10261539804751606712893997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6841026536501071141929331 10261539804751606712893997)
                    ·
                      refine ⟨3848077426781852517335249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261539804751606712893997 3848077426781852517335249)
                      ·
                        rfl

theorem cell23_7494104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_7494104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494104 prefixEnd_7494104 := by exact prefixLift 7494104
  have htrace : WordTrace (prefixWord ++ tailWord_7494104) baseStart_7494104 baseEnd_7494104 := by
    simpa [prefixWord, tailWord_7494104, baseEnd_7494104] using wordTrace_append hprefix tailTrace_7494104
  have hstable : (prefixWord ++ tailWord_7494104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494104).length < 2 ^ (prefixWord ++ tailWord_7494104).sum := by decide
  have hdescent : baseEnd_7494104 < baseStart_7494104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494137 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_7494137 : Nat := 118140960795 + 7494137 * 2 ^ 59
def prefixEnd_7494137 : Nat := 4983230072969 + 3 ^ 40 * 7494137 * 2
def baseEnd_7494137 : Nat := 1282698123881150296074199

theorem tailTrace_7494137 : CollatzResearch.WordTrace tailWord_7494137 prefixEnd_7494137 1282698123881150296074199 := by
  unfold tailWord_7494137
  simp only [CollatzResearch.WordTrace]
  refine ⟨273333631651029020546928665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182222421100686013697952443 273333631651029020546928665)
  ·
    refine ⟨205000223738271765410196499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273333631651029020546928665 205000223738271765410196499)
    ·
      refine ⟨307500335607407648115294749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205000223738271765410196499 307500335607407648115294749)
      ·
        refine ⟨115312625852777868043235531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307500335607407648115294749 115312625852777868043235531)
        ·
          refine ⟨172968938779166802064853297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115312625852777868043235531 172968938779166802064853297)
          ·
            refine ⟨129726704084375101548639973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172968938779166802064853297 129726704084375101548639973)
            ·
              refine ⟨24323757015820331540369995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129726704084375101548639973 24323757015820331540369995)
              ·
                refine ⟨36485635523730497310554993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24323757015820331540369995 36485635523730497310554993)
                ·
                  refine ⟨27364226642797872982916245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36485635523730497310554993 27364226642797872982916245)
                  ·
                    refine ⟨1282698123881150296074199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27364226642797872982916245 1282698123881150296074199)
                    ·
                      rfl

theorem cell23_7494137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_7494137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494137 prefixEnd_7494137 := by exact prefixLift 7494137
  have htrace : WordTrace (prefixWord ++ tailWord_7494137) baseStart_7494137 baseEnd_7494137 := by
    simpa [prefixWord, tailWord_7494137, baseEnd_7494137] using wordTrace_append hprefix tailTrace_7494137
  have hstable : (prefixWord ++ tailWord_7494137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494137).length < 2 ^ (prefixWord ++ tailWord_7494137).sum := by decide
  have hdescent : baseEnd_7494137 < baseStart_7494137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494147 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_7494147 : Nat := 118140960795 + 7494147 * 2 ^ 59
def prefixEnd_7494147 : Nat := 4983230072969 + 3 ^ 40 * 7494147 * 2
def baseEnd_7494147 : Nat := 3848099506449995849097551

theorem tailTrace_7494147 : CollatzResearch.WordTrace tailWord_7494147 prefixEnd_7494147 3848099506449995849097551 := by
  unfold tailWord_7494147
  simp only [CollatzResearch.WordTrace]
  refine ⟨273333996380992792254792695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182222664253995194836528463 273333996380992792254792695)
  ·
    refine ⟨410000994571489188382189043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273333996380992792254792695 410000994571489188382189043)
    ·
      refine ⟨615001491857233782573283565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410000994571489188382189043 615001491857233782573283565)
      ·
        refine ⟨230625559446462668464981337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615001491857233782573283565 230625559446462668464981337)
        ·
          refine ⟨172969169584847001348736003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230625559446462668464981337 172969169584847001348736003)
          ·
            refine ⟨259453754377270502023104005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172969169584847001348736003 259453754377270502023104005)
            ·
              refine ⟨48647578945738219129332001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259453754377270502023104005 48647578945738219129332001)
              ·
                refine ⟨36485684209303664346999001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48647578945738219129332001 36485684209303664346999001)
                ·
                  refine ⟨27364263156977748260249251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36485684209303664346999001 27364263156977748260249251)
                  ·
                    refine ⟨41046394735466622390373877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27364263156977748260249251 41046394735466622390373877)
                    ·
                      refine ⟨3848099506449995849097551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41046394735466622390373877 3848099506449995849097551)
                      ·
                        rfl

theorem cell23_7494147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_7494147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494147 prefixEnd_7494147 := by exact prefixLift 7494147
  have htrace : WordTrace (prefixWord ++ tailWord_7494147) baseStart_7494147 baseEnd_7494147 := by
    simpa [prefixWord, tailWord_7494147, baseEnd_7494147] using wordTrace_append hprefix tailTrace_7494147
  have hstable : (prefixWord ++ tailWord_7494147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494147).length < 2 ^ (prefixWord ++ tailWord_7494147).sum := by decide
  have hdescent : baseEnd_7494147 < baseStart_7494147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494148 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7494148 : Nat := 118140960795 + 7494148 * 2 ^ 59
def prefixEnd_7494148 : Nat := 4983230072969 + 3 ^ 40 * 7494148 * 2
def baseEnd_7494148 : Nat := 3848100019930650345185047

theorem tailTrace_7494148 : CollatzResearch.WordTrace tailWord_7494148 prefixEnd_7494148 3848100019930650345185047 := by
  unfold tailWord_7494148
  simp only [CollatzResearch.WordTrace]
  refine ⟨136667016426994584712789549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182222688569326112950386065 136667016426994584712789549)
  ·
    refine ⟨51250131160122969267296081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136667016426994584712789549 51250131160122969267296081)
    ·
      refine ⟨38437598370092226950472061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51250131160122969267296081 38437598370092226950472061)
      ·
        refine ⟨14414099388784585106427023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38437598370092226950472061 14414099388784585106427023)
        ·
          refine ⟨21621149083176877659640535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414099388784585106427023 21621149083176877659640535)
          ·
            refine ⟨32431723624765316489460803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21621149083176877659640535 32431723624765316489460803)
            ·
              refine ⟨48647585437147974734191205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32431723624765316489460803 48647585437147974734191205)
              ·
                refine ⟨9121422269465245262660851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48647585437147974734191205 9121422269465245262660851)
                ·
                  refine ⟨13682133404197867893991277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121422269465245262660851 13682133404197867893991277)
                  ·
                    refine ⟨5130800026574200460246729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13682133404197867893991277 5130800026574200460246729)
                    ·
                      refine ⟨3848100019930650345185047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130800026574200460246729 3848100019930650345185047)
                      ·
                        rfl

theorem cell23_7494148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7494148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494148 prefixEnd_7494148 := by exact prefixLift 7494148
  have htrace : WordTrace (prefixWord ++ tailWord_7494148) baseStart_7494148 baseEnd_7494148 := by
    simpa [prefixWord, tailWord_7494148, baseEnd_7494148] using wordTrace_append hprefix tailTrace_7494148
  have hstable : (prefixWord ++ tailWord_7494148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494148).length < 2 ^ (prefixWord ++ tailWord_7494148).sum := by decide
  have hdescent : baseEnd_7494148 < baseStart_7494148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494177 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7494177 : Nat := 118140960795 + 7494177 * 2 ^ 59
def prefixEnd_7494177 : Nat := 4983230072969 + 3 ^ 40 * 7494177 * 2
def baseEnd_7494177 : Nat := 3848114910869630731722413

theorem tailTrace_7494177 : CollatzResearch.WordTrace tailWord_7494177 prefixEnd_7494177 3848114910869630731722413 := by
  unfold tailWord_7494177
  simp only [CollatzResearch.WordTrace]
  refine ⟨273335090570884107378384785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182223393713922738252256523 273335090570884107378384785)
  ·
    refine ⟨205001317928163080533788589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273335090570884107378384785 205001317928163080533788589)
    ·
      refine ⟨76875494223061155200170721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205001317928163080533788589 76875494223061155200170721)
      ·
        refine ⟨57656620667295866400128041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76875494223061155200170721 57656620667295866400128041)
        ·
          refine ⟨43242465500471899800096031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57656620667295866400128041 43242465500471899800096031)
          ·
            refine ⟨64863698250707849700144047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43242465500471899800096031 64863698250707849700144047)
            ·
              refine ⟨97295547376061774550216071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64863698250707849700144047 97295547376061774550216071)
              ·
                refine ⟨145943321064092661825324107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97295547376061774550216071 145943321064092661825324107)
                ·
                  refine ⟨218914981596138992737986161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145943321064092661825324107 218914981596138992737986161)
                  ·
                    refine ⟨164186236197104244553489621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218914981596138992737986161 164186236197104244553489621)
                    ·
                      refine ⟨3848114910869630731722413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164186236197104244553489621 3848114910869630731722413)
                      ·
                        rfl

theorem cell23_7494177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7494177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494177 prefixEnd_7494177 := by exact prefixLift 7494177
  have htrace : WordTrace (prefixWord ++ tailWord_7494177) baseStart_7494177 baseEnd_7494177 := by
    simpa [prefixWord, tailWord_7494177, baseEnd_7494177] using wordTrace_append hprefix tailTrace_7494177
  have hstable : (prefixWord ++ tailWord_7494177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494177).length < 2 ^ (prefixWord ++ tailWord_7494177).sum := by decide
  have hdescent : baseEnd_7494177 < baseStart_7494177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494178 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_7494178 : Nat := 118140960795 + 7494178 * 2 ^ 59
def prefixEnd_7494178 : Nat := 4983230072969 + 3 ^ 40 * 7494178 * 2
def baseEnd_7494178 : Nat := 3848115424350285227809909

theorem tailTrace_7494178 : CollatzResearch.WordTrace tailWord_7494178 prefixEnd_7494178 3848115424350285227809909 := by
  unfold tailWord_7494178
  simp only [CollatzResearch.WordTrace]
  refine ⟨68333781760970121137292797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182223418029253656366114125 68333781760970121137292797)
  ·
    refine ⟨25625168160363795426484799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68333781760970121137292797 25625168160363795426484799)
    ·
      refine ⟨38437752240545693139727199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25625168160363795426484799 38437752240545693139727199)
      ·
        refine ⟨57656628360818539709590799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38437752240545693139727199 57656628360818539709590799)
        ·
          refine ⟨86484942541227809564386199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57656628360818539709590799 86484942541227809564386199)
          ·
            refine ⟨129727413811841714346579299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86484942541227809564386199 129727413811841714346579299)
            ·
              refine ⟨194591120717762571519868949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129727413811841714346579299 194591120717762571519868949)
              ·
                refine ⟨9121458783645120539993857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194591120717762571519868949 9121458783645120539993857)
                ·
                  refine ⟨6841094087733840404995393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9121458783645120539993857 6841094087733840404995393)
                  ·
                    refine ⟨5130820565800380303746545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6841094087733840404995393 5130820565800380303746545)
                    ·
                      refine ⟨3848115424350285227809909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130820565800380303746545 3848115424350285227809909)
                      ·
                        rfl

theorem cell23_7494178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_7494178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494178 prefixEnd_7494178 := by exact prefixLift 7494178
  have htrace : WordTrace (prefixWord ++ tailWord_7494178) baseStart_7494178 baseEnd_7494178 := by
    simpa [prefixWord, tailWord_7494178, baseEnd_7494178] using wordTrace_append hprefix tailTrace_7494178
  have hstable : (prefixWord ++ tailWord_7494178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494178).length < 2 ^ (prefixWord ++ tailWord_7494178).sum := by decide
  have hdescent : baseEnd_7494178 < baseStart_7494178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494194 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_7494194 : Nat := 118140960795 + 7494194 * 2 ^ 59
def prefixEnd_7494194 : Nat := 4983230072969 + 3 ^ 40 * 7494194 * 2
def baseEnd_7494194 : Nat := 3848123640040757165209835

theorem tailTrace_7494194 : CollatzResearch.WordTrace tailWord_7494194 prefixEnd_7494194 3848123640040757165209835 := by
  unfold tailWord_7494194
  simp only [CollatzResearch.WordTrace]
  refine ⟨68333927652955629820438409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182223807074548346187835757 68333927652955629820438409)
  ·
    refine ⟨51250445739716722365328807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68333927652955629820438409 51250445739716722365328807)
    ·
      refine ⟨76875668609575083547993211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51250445739716722365328807 76875668609575083547993211)
      ·
        refine ⟨115313502914362625321989817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76875668609575083547993211 115313502914362625321989817)
        ·
          refine ⟨86485127185771968991492363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115313502914362625321989817 86485127185771968991492363)
          ·
            refine ⟨129727690778657953487238545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86485127185771968991492363 129727690778657953487238545)
            ·
              refine ⟨97295768083993465115428909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129727690778657953487238545 97295768083993465115428909)
              ·
                refine ⟨36485913031497549418285841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97295768083993465115428909 36485913031497549418285841)
                ·
                  refine ⟨27364434773623162063714381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36485913031497549418285841 27364434773623162063714381)
                  ·
                    refine ⟨10261663040108685773892893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27364434773623162063714381 10261663040108685773892893)
                    ·
                      refine ⟨3848123640040757165209835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261663040108685773892893 3848123640040757165209835)
                      ·
                        rfl

theorem cell23_7494194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_7494194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494194 prefixEnd_7494194 := by exact prefixLift 7494194
  have htrace : WordTrace (prefixWord ++ tailWord_7494194) baseStart_7494194 baseEnd_7494194 := by
    simpa [prefixWord, tailWord_7494194, baseEnd_7494194] using wordTrace_append hprefix tailTrace_7494194
  have hstable : (prefixWord ++ tailWord_7494194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494194).length < 2 ^ (prefixWord ++ tailWord_7494194).sum := by decide
  have hdescent : baseEnd_7494194 < baseStart_7494194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494207 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_7494207 : Nat := 118140960795 + 7494207 * 2 ^ 59
def prefixEnd_7494207 : Nat := 4983230072969 + 3 ^ 40 * 7494207 * 2
def baseEnd_7494207 : Nat := 3848130315289265614347275

theorem tailTrace_7494207 : CollatzResearch.WordTrace tailWord_7494207 prefixEnd_7494207 3848130315289265614347275 := by
  unfold tailWord_7494207
  simp only [CollatzResearch.WordTrace]
  refine ⟨273336184760775422501976875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182224123173850281667984583 273336184760775422501976875)
  ·
    refine ⟨410004277141163133752965313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273336184760775422501976875 410004277141163133752965313)
    ·
      refine ⟨307503207855872350314723985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410004277141163133752965313 307503207855872350314723985)
      ·
        refine ⟨230627405891904262736042989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307503207855872350314723985 230627405891904262736042989)
        ·
          refine ⟨86485277209464098526016121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230627405891904262736042989 86485277209464098526016121)
          ·
            refine ⟨64863957907098073894512091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86485277209464098526016121 64863957907098073894512091)
            ·
              refine ⟨97295936860647110841768137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64863957907098073894512091 97295936860647110841768137)
              ·
                refine ⟨72971952645485333131326103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97295936860647110841768137 72971952645485333131326103)
                ·
                  refine ⟨109457928968227999696989155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72971952645485333131326103 109457928968227999696989155)
                  ·
                    refine ⟨164186893452341999545483733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109457928968227999696989155 164186893452341999545483733)
                    ·
                      refine ⟨3848130315289265614347275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164186893452341999545483733 3848130315289265614347275)
                      ·
                        rfl

theorem cell23_7494207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_7494207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494207 prefixEnd_7494207 := by exact prefixLift 7494207
  have htrace : WordTrace (prefixWord ++ tailWord_7494207) baseStart_7494207 baseEnd_7494207 := by
    simpa [prefixWord, tailWord_7494207, baseEnd_7494207] using wordTrace_append hprefix tailTrace_7494207
  have hstable : (prefixWord ++ tailWord_7494207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494207).length < 2 ^ (prefixWord ++ tailWord_7494207).sum := by decide
  have hdescent : baseEnd_7494207 < baseStart_7494207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494212 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7494212 : Nat := 118140960795 + 7494212 * 2 ^ 59
def prefixEnd_7494212 : Nat := 4983230072969 + 3 ^ 40 * 7494212 * 2
def baseEnd_7494212 : Nat := 3848132882692538094784753

theorem tailTrace_7494212 : CollatzResearch.WordTrace tailWord_7494212 prefixEnd_7494212 3848132882692538094784753 := by
  unfold tailWord_7494212
  simp only [CollatzResearch.WordTrace]
  refine ⟨136668183562878654177954445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182224244750504872237272593 136668183562878654177954445)
  ·
    refine ⟨51250568836079495316732917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136668183562878654177954445 51250568836079495316732917)
    ·
      refine ⟨4804740828382452685943711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51250568836079495316732917 4804740828382452685943711)
      ·
        refine ⟨7207111242573679028915567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804740828382452685943711 7207111242573679028915567)
        ·
          refine ⟨10810666863860518543373351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207111242573679028915567 10810666863860518543373351)
          ·
            refine ⟨16216000295790777815060027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10810666863860518543373351 16216000295790777815060027)
            ·
              refine ⟨24324000443686166722590041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16216000295790777815060027 24324000443686166722590041)
              ·
                refine ⟨18243000332764625041942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24324000443686166722590041 18243000332764625041942531)
                ·
                  refine ⟨27364500499146937562913797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18243000332764625041942531 27364500499146937562913797)
                  ·
                    refine ⟨5130843843590050793046337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27364500499146937562913797 5130843843590050793046337)
                    ·
                      refine ⟨3848132882692538094784753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5130843843590050793046337 3848132882692538094784753)
                      ·
                        rfl

theorem cell23_7494212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7494212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494212 prefixEnd_7494212 := by exact prefixLift 7494212
  have htrace : WordTrace (prefixWord ++ tailWord_7494212) baseStart_7494212 baseEnd_7494212 := by
    simpa [prefixWord, tailWord_7494212, baseEnd_7494212] using wordTrace_append hprefix tailTrace_7494212
  have hstable : (prefixWord ++ tailWord_7494212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494212).length < 2 ^ (prefixWord ++ tailWord_7494212).sum := by decide
  have hdescent : baseEnd_7494212 < baseStart_7494212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494257 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 12]
def baseStart_7494257 : Nat := 118140960795 + 7494257 * 2 ^ 59
def prefixEnd_7494257 : Nat := 4983230072969 + 3 ^ 40 * 7494257 * 2
def baseEnd_7494257 : Nat := 427572887702443379858005

theorem tailTrace_7494257 : CollatzResearch.WordTrace tailWord_7494257 prefixEnd_7494257 427572887702443379858005 := by
  unfold tailWord_7494257
  simp only [CollatzResearch.WordTrace]
  refine ⟨273338008410594281041297025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182225338940396187360864683 273338008410594281041297025)
  ·
    refine ⟨205003506307945710780972769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273338008410594281041297025 205003506307945710780972769)
    ·
      refine ⟨153752629730959283085729577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205003506307945710780972769 153752629730959283085729577)
      ·
        refine ⟨115314472298219462314297183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153752629730959283085729577 115314472298219462314297183)
        ·
          refine ⟨172971708447329193471445775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115314472298219462314297183 172971708447329193471445775)
          ·
            refine ⟨259457562670993790207168663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172971708447329193471445775 259457562670993790207168663)
            ·
              refine ⟨389186344006490685310752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259457562670993790207168663 389186344006490685310752995)
              ·
                refine ⟨583779516009736027966129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389186344006490685310752995 583779516009736027966129493)
                ·
                  refine ⟨427572887702443379858005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 583779516009736027966129493 427572887702443379858005)
                  ·
                    rfl

theorem cell23_7494257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_7494257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494257 prefixEnd_7494257 := by exact prefixLift 7494257
  have htrace : WordTrace (prefixWord ++ tailWord_7494257) baseStart_7494257 baseEnd_7494257 := by
    simpa [prefixWord, tailWord_7494257, baseEnd_7494257] using wordTrace_append hprefix tailTrace_7494257
  have hstable : (prefixWord ++ tailWord_7494257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494257).length < 2 ^ (prefixWord ++ tailWord_7494257).sum := by decide
  have hdescent : baseEnd_7494257 < baseStart_7494257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494335 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 1, 1, 3]
def baseStart_7494335 : Nat := 118140960795 + 7494335 * 2 ^ 59
def prefixEnd_7494335 : Nat := 4983230072969 + 3 ^ 40 * 7494335 * 2
def baseEnd_7494335 : Nat := 3848196040813041113546687

theorem tailTrace_7494335 : CollatzResearch.WordTrace tailWord_7494335 prefixEnd_7494335 3848196040813041113546687 := by
  unfold tailWord_7494335
  simp only [CollatzResearch.WordTrace]
  refine ⟨273340853304311700362636459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182227235536207800241757639 273340853304311700362636459)
  ·
    refine ⟨410011279956467550543954689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273340853304311700362636459 410011279956467550543954689)
    ·
      refine ⟨307508459967350662907966017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410011279956467550543954689 307508459967350662907966017)
      ·
        refine ⟨230631344975512997180974513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307508459967350662907966017 230631344975512997180974513)
        ·
          refine ⟨172973508731634747885730885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230631344975512997180974513 172973508731634747885730885)
          ·
            refine ⟨32432532887181515228574541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172973508731634747885730885 32432532887181515228574541)
            ·
              refine ⟨12162199832693068210715453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32432532887181515228574541 12162199832693068210715453)
              ·
                refine ⟨4560824937259900579018295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12162199832693068210715453 4560824937259900579018295)
                ·
                  refine ⟨6841237405889850868527443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560824937259900579018295 6841237405889850868527443)
                  ·
                    refine ⟨10261856108834776302791165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6841237405889850868527443 10261856108834776302791165)
                    ·
                      refine ⟨3848196040813041113546687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261856108834776302791165 3848196040813041113546687)
                      ·
                        rfl

theorem cell23_7494335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_7494335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494335 prefixEnd_7494335 := by exact prefixLift 7494335
  have htrace : WordTrace (prefixWord ++ tailWord_7494335) baseStart_7494335 baseEnd_7494335 := by
    simpa [prefixWord, tailWord_7494335, baseEnd_7494335] using wordTrace_append hprefix tailTrace_7494335
  have hstable : (prefixWord ++ tailWord_7494335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494335).length < 2 ^ (prefixWord ++ tailWord_7494335).sum := by decide
  have hdescent : baseEnd_7494335 < baseStart_7494335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494361 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_7494361 : Nat := 118140960795 + 7494361 * 2 ^ 59
def prefixEnd_7494361 : Nat := 4983230072969 + 3 ^ 40 * 7494361 * 2
def baseEnd_7494361 : Nat := 3848209391310058011821567

theorem tailTrace_7494361 : CollatzResearch.WordTrace tailWord_7494361 prefixEnd_7494361 3848209391310058011821567 := by
  unfold tailWord_7494361
  simp only [CollatzResearch.WordTrace]
  refine ⟨273341801602217506803082937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182227867734811671202055291 273341801602217506803082937)
  ·
    refine ⟨205006351201663130102312203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273341801602217506803082937 205006351201663130102312203)
    ·
      refine ⟨307509526802494695153468305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205006351201663130102312203 307509526802494695153468305)
      ·
        refine ⟨230632145101871021365101229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307509526802494695153468305 230632145101871021365101229)
        ·
          refine ⟨86487054413201633011912961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230632145101871021365101229 86487054413201633011912961)
          ·
            refine ⟨64865290809901224758934721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86487054413201633011912961 64865290809901224758934721)
            ·
              refine ⟨48648968107425918569201041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64865290809901224758934721 48648968107425918569201041)
              ·
                refine ⟨36486726080569438926900781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48648968107425918569201041 36486726080569438926900781)
                ·
                  refine ⟨13682522280213539597587793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36486726080569438926900781 13682522280213539597587793)
                  ·
                    refine ⟨10261891710160154698190845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13682522280213539597587793 10261891710160154698190845)
                    ·
                      refine ⟨3848209391310058011821567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10261891710160154698190845 3848209391310058011821567)
                      ·
                        rfl

theorem cell23_7494361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_7494361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494361 prefixEnd_7494361 := by exact prefixLift 7494361
  have htrace : WordTrace (prefixWord ++ tailWord_7494361) baseStart_7494361 baseEnd_7494361 := by
    simpa [prefixWord, tailWord_7494361, baseEnd_7494361] using wordTrace_append hprefix tailTrace_7494361
  have hstable : (prefixWord ++ tailWord_7494361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494361).length < 2 ^ (prefixWord ++ tailWord_7494361).sum := by decide
  have hdescent : baseEnd_7494361 < baseStart_7494361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494371 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7494371 : Nat := 118140960795 + 7494371 * 2 ^ 59
def prefixEnd_7494371 : Nat := 4983230072969 + 3 ^ 40 * 7494371 * 2
def baseEnd_7494371 : Nat := 3848214526116602972696521

theorem tailTrace_7494371 : CollatzResearch.WordTrace tailWord_7494371 prefixEnd_7494371 3848214526116602972696521 := by
  unfold tailWord_7494371
  simp only [CollatzResearch.WordTrace]
  refine ⟨273342166332181278510946967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182228110888120852340631311 273342166332181278510946967)
  ·
    refine ⟨410013249498271917766420451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273342166332181278510946967 410013249498271917766420451)
    ·
      refine ⟨615019874247407876649630677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410013249498271917766420451 615019874247407876649630677)
      ·
        refine ⟨14414528302673622108975719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 615019874247407876649630677 14414528302673622108975719)
        ·
          refine ⟨21621792454010433163463579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414528302673622108975719 21621792454010433163463579)
          ·
            refine ⟨32432688681015649745195369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21621792454010433163463579 32432688681015649745195369)
            ·
              refine ⟨24324516510761737308896527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32432688681015649745195369 24324516510761737308896527)
              ·
                refine ⟨36486774766142605963344791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24324516510761737308896527 36486774766142605963344791)
                ·
                  refine ⟨54730162149213908945017187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36486774766142605963344791 54730162149213908945017187)
                  ·
                    refine ⟨82095243223820863417525781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54730162149213908945017187 82095243223820863417525781)
                    ·
                      refine ⟨3848214526116602972696521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82095243223820863417525781 3848214526116602972696521)
                      ·
                        rfl

theorem cell23_7494371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7494371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494371 prefixEnd_7494371 := by exact prefixLift 7494371
  have htrace : WordTrace (prefixWord ++ tailWord_7494371) baseStart_7494371 baseEnd_7494371 := by
    simpa [prefixWord, tailWord_7494371, baseEnd_7494371] using wordTrace_append hprefix tailTrace_7494371
  have hstable : (prefixWord ++ tailWord_7494371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494371).length < 2 ^ (prefixWord ++ tailWord_7494371).sum := by decide
  have hdescent : baseEnd_7494371 < baseStart_7494371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494389 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7494389 : Nat := 118140960795 + 7494389 * 2 ^ 59
def prefixEnd_7494389 : Nat := 4983230072969 + 3 ^ 40 * 7494389 * 2
def baseEnd_7494389 : Nat := 1282741256256127967423813

theorem tailTrace_7494389 : CollatzResearch.WordTrace tailWord_7494389 prefixEnd_7494389 1282741256256127967423813 := by
  unfold tailWord_7494389
  simp only [CollatzResearch.WordTrace]
  refine ⟨273342822846116067585102221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182228548564077378390068147 273342822846116067585102221)
  ·
    refine ⟨102503558567293525344413333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273342822846116067585102221 102503558567293525344413333)
    ·
      refine ⟨4804854307841884000519375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102503558567293525344413333 4804854307841884000519375)
      ·
        refine ⟨7207281461762826000779063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804854307841884000519375 7207281461762826000779063)
        ·
          refine ⟨10810922192644239001168595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207281461762826000779063 10810922192644239001168595)
          ·
            refine ⟨16216383288966358501752893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10810922192644239001168595 16216383288966358501752893)
            ·
              refine ⟨6081143733362384438157335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16216383288966358501752893 6081143733362384438157335)
              ·
                refine ⟨9121715600043576657236003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081143733362384438157335 9121715600043576657236003)
                ·
                  refine ⟨13682573400065364985854005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121715600043576657236003 13682573400065364985854005)
                  ·
                    refine ⟨1282741256256127967423813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13682573400065364985854005 1282741256256127967423813)
                    ·
                      rfl

theorem cell23_7494389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7494389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494389 prefixEnd_7494389 := by exact prefixLift 7494389
  have htrace : WordTrace (prefixWord ++ tailWord_7494389) baseStart_7494389 baseEnd_7494389 := by
    simpa [prefixWord, tailWord_7494389, baseEnd_7494389] using wordTrace_append hprefix tailTrace_7494389
  have hstable : (prefixWord ++ tailWord_7494389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494389).length < 2 ^ (prefixWord ++ tailWord_7494389).sum := by decide
  have hdescent : baseEnd_7494389 < baseStart_7494389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494501 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_7494501 : Nat := 118140960795 + 7494501 * 2 ^ 59
def prefixEnd_7494501 : Nat := 4983230072969 + 3 ^ 40 * 7494501 * 2
def baseEnd_7494501 : Nat := 1282760426200562488023641

theorem tailTrace_7494501 : CollatzResearch.WordTrace tailWord_7494501 prefixEnd_7494501 1282760426200562488023641 := by
  unfold tailWord_7494501
  simp only [CollatzResearch.WordTrace]
  refine ⟨273346907821710310713179357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182231271881140207142119571 273346907821710310713179357)
  ·
    refine ⟨102505090433141366517442259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273346907821710310713179357 102505090433141366517442259)
    ·
      refine ⟨153757635649712049776163389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102505090433141366517442259 153757635649712049776163389)
      ·
        refine ⟨57659113368642018666061271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153757635649712049776163389 57659113368642018666061271)
        ·
          refine ⟨86488670052963027999091907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57659113368642018666061271 86488670052963027999091907)
          ·
            refine ⟨129733005079444541998637861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86488670052963027999091907 129733005079444541998637861)
            ·
              refine ⟨24324938452395851624744599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129733005079444541998637861 24324938452395851624744599)
              ·
                refine ⟨36487407678593777437116899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24324938452395851624744599 36487407678593777437116899)
                ·
                  refine ⟨54731111517890666155675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36487407678593777437116899 54731111517890666155675349)
                  ·
                    refine ⟨1282760426200562488023641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54731111517890666155675349 1282760426200562488023641)
                    ·
                      rfl

theorem cell23_7494501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_7494501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494501 prefixEnd_7494501 := by exact prefixLift 7494501
  have htrace : WordTrace (prefixWord ++ tailWord_7494501) baseStart_7494501 baseEnd_7494501 := by
    simpa [prefixWord, tailWord_7494501, baseEnd_7494501] using wordTrace_append hprefix tailTrace_7494501
  have hstable : (prefixWord ++ tailWord_7494501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494501).length < 2 ^ (prefixWord ++ tailWord_7494501).sum := by decide
  have hdescent : baseEnd_7494501 < baseStart_7494501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494608 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_7494608 : Nat := 118140960795 + 7494608 * 2 ^ 59
def prefixEnd_7494608 : Nat := 4983230072969 + 3 ^ 40 * 7494608 * 2
def baseEnd_7494608 : Nat := 1282778740343906181810977

theorem tailTrace_7494608 : CollatzResearch.WordTrace tailWord_7494608 prefixEnd_7494608 1282778740343906181810977 := by
  unfold tailWord_7494608
  simp only [CollatzResearch.WordTrace]
  refine ⟨136675405216161333993662239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182233873621548445324882985 136675405216161333993662239)
  ·
    refine ⟨205013107824242000990493359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136675405216161333993662239 205013107824242000990493359)
    ·
      refine ⟨307519661736363001485740039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205013107824242000990493359 307519661736363001485740039)
      ·
        refine ⟨461279492604544502228610059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307519661736363001485740039 461279492604544502228610059)
        ·
          refine ⟨691919238906816753342915089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461279492604544502228610059 691919238906816753342915089)
          ·
            refine ⟨518939429180112565007186317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691919238906816753342915089 518939429180112565007186317)
            ·
              refine ⟨194602285942542211877694869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518939429180112565007186317 194602285942542211877694869)
              ·
                refine ⟨9121982153556666181766947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194602285942542211877694869 9121982153556666181766947)
                ·
                  refine ⟨13682973230334999272650421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121982153556666181766947 13682973230334999272650421)
                  ·
                    refine ⟨1282778740343906181810977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13682973230334999272650421 1282778740343906181810977)
                    ·
                      rfl

theorem cell23_7494608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_7494608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494608 prefixEnd_7494608 := by exact prefixLift 7494608
  have htrace : WordTrace (prefixWord ++ tailWord_7494608) baseStart_7494608 baseEnd_7494608 := by
    simpa [prefixWord, tailWord_7494608, baseEnd_7494608] using wordTrace_append hprefix tailTrace_7494608
  have hstable : (prefixWord ++ tailWord_7494608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494608).length < 2 ^ (prefixWord ++ tailWord_7494608).sum := by decide
  have hdescent : baseEnd_7494608 < baseStart_7494608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494615 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_7494615 : Nat := 118140960795 + 7494615 * 2 ^ 59
def prefixEnd_7494615 : Nat := 4983230072969 + 3 ^ 40 * 7494615 * 2
def baseEnd_7494615 : Nat := 3848339815396300018045399

theorem tailTrace_7494615 : CollatzResearch.WordTrace tailWord_7494615 prefixEnd_7494615 3848339815396300018045399 := by
  unfold tailWord_7494615
  simp only [CollatzResearch.WordTrace]
  refine ⟨273351065743297308182829299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182234043828864872121886199 273351065743297308182829299)
  ·
    refine ⟨410026598614945962274243949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273351065743297308182829299 410026598614945962274243949)
    ·
      refine ⟨153759974480604735852841481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410026598614945962274243949 153759974480604735852841481)
      ·
        refine ⟨115319980860453551889631111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153759974480604735852841481 115319980860453551889631111)
        ·
          refine ⟨172979971290680327834446667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115319980860453551889631111 172979971290680327834446667)
          ·
            refine ⟨259469956936020491751670001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172979971290680327834446667 259469956936020491751670001)
            ·
              refine ⟨194602467702015368813752501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259469956936020491751670001 194602467702015368813752501)
              ·
                refine ⟨18243981347063940826289297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194602467702015368813752501 18243981347063940826289297)
                ·
                  refine ⟨13682986010297955619716973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18243981347063940826289297 13682986010297955619716973)
                  ·
                    refine ⟨5131119753861733357393865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13682986010297955619716973 5131119753861733357393865)
                    ·
                      refine ⟨3848339815396300018045399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131119753861733357393865 3848339815396300018045399)
                      ·
                        rfl

theorem cell23_7494615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_7494615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494615 prefixEnd_7494615 := by exact prefixLift 7494615
  have htrace : WordTrace (prefixWord ++ tailWord_7494615) baseStart_7494615 baseEnd_7494615 := by
    simpa [prefixWord, tailWord_7494615, baseEnd_7494615] using wordTrace_append hprefix tailTrace_7494615
  have hstable : (prefixWord ++ tailWord_7494615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494615).length < 2 ^ (prefixWord ++ tailWord_7494615).sum := by decide
  have hdescent : baseEnd_7494615 < baseStart_7494615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494628 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_7494628 : Nat := 118140960795 + 7494628 * 2 ^ 59
def prefixEnd_7494628 : Nat := 4983230072969 + 3 ^ 40 * 7494628 * 2
def baseEnd_7494628 : Nat := 3848346490644808467182839

theorem tailTrace_7494628 : CollatzResearch.WordTrace tailWord_7494628 prefixEnd_7494628 3848346490644808467182839 := by
  unfold tailWord_7494628
  simp only [CollatzResearch.WordTrace]
  refine ⟨136675769946125105701526269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182234359928166807602035025 136675769946125105701526269)
  ·
    refine ⟨51253413729796914638072351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136675769946125105701526269 51253413729796914638072351)
    ·
      refine ⟨76880120594695371957108527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51253413729796914638072351 76880120594695371957108527)
      ·
        refine ⟨115320180892043057935662791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76880120594695371957108527 115320180892043057935662791)
        ·
          refine ⟨172980271338064586903494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115320180892043057935662791 172980271338064586903494187)
          ·
            refine ⟨259470407007096880355241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172980271338064586903494187 259470407007096880355241281)
            ·
              refine ⟨194602805255322660266430961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259470407007096880355241281 194602805255322660266430961)
              ·
                refine ⟨145952103941491995199823221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194602805255322660266430961 145952103941491995199823221)
                ·
                  refine ⟨13683009744514874549983427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145952103941491995199823221 13683009744514874549983427)
                  ·
                    refine ⟨20524514616772311824975141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13683009744514874549983427 20524514616772311824975141)
                    ·
                      refine ⟨3848346490644808467182839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20524514616772311824975141 3848346490644808467182839)
                      ·
                        rfl

theorem cell23_7494628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_7494628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494628 prefixEnd_7494628 := by exact prefixLift 7494628
  have htrace : WordTrace (prefixWord ++ tailWord_7494628) baseStart_7494628 baseEnd_7494628 := by
    simpa [prefixWord, tailWord_7494628, baseEnd_7494628] using wordTrace_append hprefix tailTrace_7494628
  have hstable : (prefixWord ++ tailWord_7494628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494628).length < 2 ^ (prefixWord ++ tailWord_7494628).sum := by decide
  have hdescent : baseEnd_7494628 < baseStart_7494628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494629 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 6]
def baseStart_7494629 : Nat := 118140960795 + 7494629 * 2 ^ 59
def prefixEnd_7494629 : Nat := 4983230072969 + 3 ^ 40 * 7494629 * 2
def baseEnd_7494629 : Nat := 427594111569495884807815

theorem tailTrace_7494629 : CollatzResearch.WordTrace tailWord_7494629 prefixEnd_7494629 427594111569495884807815 := by
  unfold tailWord_7494629
  simp only [CollatzResearch.WordTrace]
  refine ⟨273351576365246588573838941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182234384243497725715892627 273351576365246588573838941)
  ·
    refine ⟨102506841136967470715189603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273351576365246588573838941 102506841136967470715189603)
    ·
      refine ⟨153760261705451206072784405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102506841136967470715189603 153760261705451206072784405)
      ·
        refine ⟨7207512267443025284661769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153760261705451206072784405 7207512267443025284661769)
        ·
          refine ⟨5405634200582268963496327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207512267443025284661769 5405634200582268963496327)
          ·
            refine ⟨8108451300873403445244491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405634200582268963496327 8108451300873403445244491)
            ·
              refine ⟨12162676951310105167866737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108451300873403445244491 12162676951310105167866737)
              ·
                refine ⟨9122007713482578875900053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12162676951310105167866737 9122007713482578875900053)
                ·
                  refine ⟨427594111569495884807815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9122007713482578875900053 427594111569495884807815)
                  ·
                    rfl

theorem cell23_7494629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_7494629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494629 prefixEnd_7494629 := by exact prefixLift 7494629
  have htrace : WordTrace (prefixWord ++ tailWord_7494629) baseStart_7494629 baseEnd_7494629 := by
    simpa [prefixWord, tailWord_7494629, baseEnd_7494629] using wordTrace_append hprefix tailTrace_7494629
  have hstable : (prefixWord ++ tailWord_7494629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494629).length < 2 ^ (prefixWord ++ tailWord_7494629).sum := by decide
  have hdescent : baseEnd_7494629 < baseStart_7494629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494651 : List Nat := [1, 1, 1, 1, 1, 3, 3, 12]
def baseStart_7494651 : Nat := 118140960795 + 7494651 * 2 ^ 59
def prefixEnd_7494651 : Nat := 4983230072969 + 3 ^ 40 * 7494651 * 2
def baseEnd_7494651 : Nat := 142531788914809699155379

theorem tailTrace_7494651 : CollatzResearch.WordTrace tailWord_7494651 prefixEnd_7494651 142531788914809699155379 := by
  unfold tailWord_7494651
  simp only [CollatzResearch.WordTrace]
  refine ⟨273352378771166886331139807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182234919180777924220759871 273352378771166886331139807)
  ·
    refine ⟨410028568156750329496709711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273352378771166886331139807 410028568156750329496709711)
    ·
      refine ⟨615042852235125494245064567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410028568156750329496709711 615042852235125494245064567)
      ·
        refine ⟨922564278352688241367596851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615042852235125494245064567 922564278352688241367596851)
        ·
          refine ⟨1383846417529032362051395277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922564278352688241367596851 1383846417529032362051395277)
          ·
            refine ⟨518942406573387135769273229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1383846417529032362051395277 518942406573387135769273229)
            ·
              refine ⟨194603402465020175913477461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518942406573387135769273229 194603402465020175913477461)
              ·
                refine ⟨142531788914809699155379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 194603402465020175913477461 142531788914809699155379)
                ·
                  rfl

theorem cell23_7494651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 12].length) (baseStart_7494651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494651 prefixEnd_7494651 := by exact prefixLift 7494651
  have htrace : WordTrace (prefixWord ++ tailWord_7494651) baseStart_7494651 baseEnd_7494651 := by
    simpa [prefixWord, tailWord_7494651, baseEnd_7494651] using wordTrace_append hprefix tailTrace_7494651
  have hstable : (prefixWord ++ tailWord_7494651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494651).length < 2 ^ (prefixWord ++ tailWord_7494651).sum := by decide
  have hdescent : baseEnd_7494651 < baseStart_7494651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494668 : List Nat := [2, 2, 1, 2, 3, 3, 1, 9]
def baseStart_7494668 : Nat := 118140960795 + 7494668 * 2 ^ 59
def prefixEnd_7494668 : Nat := 4983230072969 + 3 ^ 40 * 7494668 * 2
def baseEnd_7494668 : Nat := 142532112217444011506765

theorem tailTrace_7494668 : CollatzResearch.WordTrace tailWord_7494668 prefixEnd_7494668 142532112217444011506765 := by
  unfold tailWord_7494668
  simp only [CollatzResearch.WordTrace]
  refine ⟨136676499406052649117254329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182235332541403532156339105 136676499406052649117254329)
  ·
    refine ⟨102507374554539486837940747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136676499406052649117254329 102507374554539486837940747)
    ·
      refine ⟨153761061831809230256911121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102507374554539486837940747 153761061831809230256911121)
      ·
        refine ⟨115320796373856922692683341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153761061831809230256911121 115320796373856922692683341)
        ·
          refine ⟨43245298640196346009756253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115320796373856922692683341 43245298640196346009756253)
          ·
            refine ⟨16216986990073629753658595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43245298640196346009756253 16216986990073629753658595)
            ·
              refine ⟨24325480485110444630487893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16216986990073629753658595 24325480485110444630487893)
              ·
                refine ⟨142532112217444011506765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24325480485110444630487893 142532112217444011506765)
                ·
                  rfl

theorem cell23_7494668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 9].length) (baseStart_7494668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494668 prefixEnd_7494668 := by exact prefixLift 7494668
  have htrace : WordTrace (prefixWord ++ tailWord_7494668) baseStart_7494668 baseEnd_7494668 := by
    simpa [prefixWord, tailWord_7494668, baseEnd_7494668] using wordTrace_append hprefix tailTrace_7494668
  have hstable : (prefixWord ++ tailWord_7494668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494668).length < 2 ^ (prefixWord ++ tailWord_7494668).sum := by decide
  have hdescent : baseEnd_7494668 < baseStart_7494668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494685 : List Nat := [1, 4, 2, 2, 3, 2, 9]
def baseStart_7494685 : Nat := 118140960795 + 7494685 * 2 ^ 59
def prefixEnd_7494685 : Nat := 4983230072969 + 3 ^ 40 * 7494685 * 2
def baseEnd_7494685 : Nat := 47510811840026107952717

theorem tailTrace_7494685 : CollatzResearch.WordTrace tailWord_7494685 prefixEnd_7494685 47510811840026107952717 := by
  unfold tailWord_7494685
  simp only [CollatzResearch.WordTrace]
  refine ⟨273353618853043710137877509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182235745902029140091918339 273353618853043710137877509)
  ·
    refine ⟨51253803534945695650852033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273353618853043710137877509 51253803534945695650852033)
    ·
      refine ⟨38440352651209271738139025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51253803534945695650852033 38440352651209271738139025)
      ·
        refine ⟨28830264488406953803604269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38440352651209271738139025 28830264488406953803604269)
        ·
          refine ⟨10811349183152607676351601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28830264488406953803604269 10811349183152607676351601)
          ·
            refine ⟨8108511887364455757263701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811349183152607676351601 8108511887364455757263701)
            ·
              refine ⟨47510811840026107952717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8108511887364455757263701 47510811840026107952717)
              ·
                rfl

theorem cell23_7494685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 9].length) (baseStart_7494685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494685 prefixEnd_7494685 := by exact prefixLift 7494685
  have htrace : WordTrace (prefixWord ++ tailWord_7494685) baseStart_7494685 baseEnd_7494685 := by
    simpa [prefixWord, tailWord_7494685, baseEnd_7494685] using wordTrace_append hprefix tailTrace_7494685
  have hstable : (prefixWord ++ tailWord_7494685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494685).length < 2 ^ (prefixWord ++ tailWord_7494685).sum := by decide
  have hdescent : baseEnd_7494685 < baseStart_7494685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494765 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7494765 : Nat := 118140960795 + 7494765 * 2 ^ 59
def prefixEnd_7494765 : Nat := 4983230072969 + 3 ^ 40 * 7494765 * 2
def baseEnd_7494765 : Nat := 3848416837494474431169709

theorem tailTrace_7494765 : CollatzResearch.WordTrace tailWord_7494765 prefixEnd_7494765 3848416837494474431169709 := by
  unfold tailWord_7494765
  simp only [CollatzResearch.WordTrace]
  refine ⟨273356536692753883800789749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182237691128502589200526499 273356536692753883800789749)
  ·
    refine ⟨25627175314945676606324039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273356536692753883800789749 25627175314945676606324039)
    ·
      refine ⟨38440762972418514909486059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25627175314945676606324039 38440762972418514909486059)
      ·
        refine ⟨57661144458627772364229089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38440762972418514909486059 57661144458627772364229089)
        ·
          refine ⟨43245858343970829273171817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57661144458627772364229089 43245858343970829273171817)
          ·
            refine ⟨32434393757978121954878863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43245858343970829273171817 32434393757978121954878863)
            ·
              refine ⟨48651590636967182932318295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32434393757978121954878863 48651590636967182932318295)
              ·
                refine ⟨72977385955450774398477443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48651590636967182932318295 72977385955450774398477443)
                ·
                  refine ⟨109466078933176161597716165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72977385955450774398477443 109466078933176161597716165)
                  ·
                    refine ⟨20524889799970530299571781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109466078933176161597716165 20524889799970530299571781)
                    ·
                      refine ⟨3848416837494474431169709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20524889799970530299571781 3848416837494474431169709)
                      ·
                        rfl

theorem cell23_7494765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7494765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494765 prefixEnd_7494765 := by exact prefixLift 7494765
  have htrace : WordTrace (prefixWord ++ tailWord_7494765) baseStart_7494765 baseEnd_7494765 := by
    simpa [prefixWord, tailWord_7494765, baseEnd_7494765] using wordTrace_append hprefix tailTrace_7494765
  have hstable : (prefixWord ++ tailWord_7494765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494765).length < 2 ^ (prefixWord ++ tailWord_7494765).sum := by decide
  have hdescent : baseEnd_7494765 < baseStart_7494765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494802 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7494802 : Nat := 118140960795 + 7494802 * 2 ^ 59
def prefixEnd_7494802 : Nat := 4983230072969 + 3 ^ 40 * 7494802 * 2
def baseEnd_7494802 : Nat := 3848435836278690786407039

theorem tailTrace_7494802 : CollatzResearch.WordTrace tailWord_7494802 prefixEnd_7494802 3848435836278690786407039 := by
  unfold tailWord_7494802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68339471548404959779971665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182238590795746559413257773 68339471548404959779971665)
  ·
    refine ⟨51254603661303719834978749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68339471548404959779971665 51254603661303719834978749)
    ·
      refine ⟨19220476372988894938117031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51254603661303719834978749 19220476372988894938117031)
      ·
        refine ⟨28830714559483342407175547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19220476372988894938117031 28830714559483342407175547)
        ·
          refine ⟨43246071839225013610763321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28830714559483342407175547 43246071839225013610763321)
          ·
            refine ⟨32434553879418760208072491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43246071839225013610763321 32434553879418760208072491)
            ·
              refine ⟨48651830819128140312108737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32434553879418760208072491 48651830819128140312108737)
              ·
                refine ⟨36488873114346105234081553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48651830819128140312108737 36488873114346105234081553)
                ·
                  refine ⟨27366654835759578925561165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36488873114346105234081553 27366654835759578925561165)
                  ·
                    refine ⟨10262495563409842097085437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27366654835759578925561165 10262495563409842097085437)
                    ·
                      refine ⟨3848435836278690786407039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10262495563409842097085437 3848435836278690786407039)
                      ·
                        rfl

theorem cell23_7494802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7494802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494802 prefixEnd_7494802 := by exact prefixLift 7494802
  have htrace : WordTrace (prefixWord ++ tailWord_7494802) baseStart_7494802 baseEnd_7494802 := by
    simpa [prefixWord, tailWord_7494802, baseEnd_7494802] using wordTrace_append hprefix tailTrace_7494802
  have hstable : (prefixWord ++ tailWord_7494802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494802).length < 2 ^ (prefixWord ++ tailWord_7494802).sum := by decide
  have hdescent : baseEnd_7494802 < baseStart_7494802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494865 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 6]
def baseStart_7494865 : Nat := 118140960795 + 7494865 * 2 ^ 59
def prefixEnd_7494865 : Nat := 4983230072969 + 3 ^ 40 * 7494865 * 2
def baseEnd_7494865 : Nat := 427607576173324893324361

theorem tailTrace_7494865 : CollatzResearch.WordTrace tailWord_7494865 prefixEnd_7494865 427607576173324893324361 := by
  unfold tailWord_7494865
  simp only [CollatzResearch.WordTrace]
  refine ⟨273360183992391600879430049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182240122661594400586286699 273360183992391600879430049)
  ·
    refine ⟨205020137994293700659572537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273360183992391600879430049 205020137994293700659572537)
    ·
      refine ⟨153765103495720275494679403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205020137994293700659572537 153765103495720275494679403)
      ·
        refine ⟨230647655243580413242019105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153765103495720275494679403 230647655243580413242019105)
        ·
          refine ⟨172985741432685309931514329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230647655243580413242019105 172985741432685309931514329)
          ·
            refine ⟨129739306074513982448635747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172985741432685309931514329 129739306074513982448635747)
            ·
              refine ⟨194608959111770973672953621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129739306074513982448635747 194608959111770973672953621)
              ·
                refine ⟨9122294958364264390919701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194608959111770973672953621 9122294958364264390919701)
                ·
                  refine ⟨427607576173324893324361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9122294958364264390919701 427607576173324893324361)
                  ·
                    rfl

theorem cell23_7494865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_7494865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494865 prefixEnd_7494865 := by exact prefixLift 7494865
  have htrace : WordTrace (prefixWord ++ tailWord_7494865) baseStart_7494865 baseEnd_7494865 := by
    simpa [prefixWord, tailWord_7494865, baseEnd_7494865] using wordTrace_append hprefix tailTrace_7494865
  have hstable : (prefixWord ++ tailWord_7494865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494865).length < 2 ^ (prefixWord ++ tailWord_7494865).sum := by decide
  have hdescent : baseEnd_7494865 < baseStart_7494865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494869 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_7494869 : Nat := 118140960795 + 7494869 * 2 ^ 59
def prefixEnd_7494869 : Nat := 4983230072969 + 3 ^ 40 * 7494869 * 2
def baseEnd_7494869 : Nat := 1282823413160847341423077

theorem tailTrace_7494869 : CollatzResearch.WordTrace tailWord_7494869 prefixEnd_7494869 1282823413160847341423077 := by
  unfold tailWord_7494869
  simp only [CollatzResearch.WordTrace]
  refine ⟨273360329884377109562575661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182240219922918073041717107 273360329884377109562575661)
  ·
    refine ⟨102510123706641416085965873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273360329884377109562575661 102510123706641416085965873)
    ·
      refine ⟨76882592779981062064474405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102510123706641416085965873 76882592779981062064474405)
      ·
        refine ⟨14415486146246449137088951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76882592779981062064474405 14415486146246449137088951)
        ·
          refine ⟨21623229219369673705633427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14415486146246449137088951 21623229219369673705633427)
          ·
            refine ⟨32434843829054510558450141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21623229219369673705633427 32434843829054510558450141)
            ·
              refine ⟨12163066435895441459418803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32434843829054510558450141 12163066435895441459418803)
              ·
                refine ⟨18244599653843162189128205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12163066435895441459418803 18244599653843162189128205)
                ·
                  refine ⟨6841724870191185820923077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18244599653843162189128205 6841724870191185820923077)
                  ·
                    refine ⟨1282823413160847341423077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841724870191185820923077 1282823413160847341423077)
                    ·
                      rfl

theorem cell23_7494869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_7494869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494869 prefixEnd_7494869 := by exact prefixLift 7494869
  have htrace : WordTrace (prefixWord ++ tailWord_7494869) baseStart_7494869 baseEnd_7494869 := by
    simpa [prefixWord, tailWord_7494869, baseEnd_7494869] using wordTrace_append hprefix tailTrace_7494869
  have hstable : (prefixWord ++ tailWord_7494869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494869).length < 2 ^ (prefixWord ++ tailWord_7494869).sum := by decide
  have hdescent : baseEnd_7494869 < baseStart_7494869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494920 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 1, 4]
def baseStart_7494920 : Nat := 118140960795 + 7494920 * 2 ^ 59
def prefixEnd_7494920 : Nat := 4983230072969 + 3 ^ 40 * 7494920 * 2
def baseEnd_7494920 : Nat := 1282832142331973774910499

theorem tailTrace_7494920 : CollatzResearch.WordTrace tailWord_7494920 prefixEnd_7494920 1282832142331973774910499 := by
  unfold tailWord_7494920
  simp only [CollatzResearch.WordTrace]
  refine ⟨136681095003596172636341107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182241460004794896848454809 136681095003596172636341107)
  ·
    refine ⟨205021642505394258954511661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136681095003596172636341107 205021642505394258954511661)
    ·
      refine ⟨76883115939522847107941873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205021642505394258954511661 76883115939522847107941873)
      ·
        refine ⟨57662336954642135330956405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76883115939522847107941873 57662336954642135330956405)
        ·
          refine ⟨5405844089497700187277163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57662336954642135330956405 5405844089497700187277163)
          ·
            refine ⟨8108766134246550280915745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405844089497700187277163 8108766134246550280915745)
            ·
              refine ⟨6081574600684912710686809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8108766134246550280915745 6081574600684912710686809)
              ·
                refine ⟨4561180950513684533015107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081574600684912710686809 4561180950513684533015107)
                ·
                  refine ⟨6841771425770526799522661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561180950513684533015107 6841771425770526799522661)
                  ·
                    refine ⟨1282832142331973774910499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6841771425770526799522661 1282832142331973774910499)
                    ·
                      rfl

theorem cell23_7494920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_7494920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494920 prefixEnd_7494920 := by exact prefixLift 7494920
  have htrace : WordTrace (prefixWord ++ tailWord_7494920) baseStart_7494920 baseEnd_7494920 := by
    simpa [prefixWord, tailWord_7494920, baseEnd_7494920] using wordTrace_append hprefix tailTrace_7494920
  have hstable : (prefixWord ++ tailWord_7494920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494920).length < 2 ^ (prefixWord ++ tailWord_7494920).sum := by decide
  have hdescent : baseEnd_7494920 < baseStart_7494920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494983 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_7494983 : Nat := 118140960795 + 7494983 * 2 ^ 59
def prefixEnd_7494983 : Nat := 4983230072969 + 3 ^ 40 * 7494983 * 2
def baseEnd_7494983 : Nat := 3848528776277154578243707

theorem tailTrace_7494983 : CollatzResearch.WordTrace tailWord_7494983 prefixEnd_7494983 3848528776277154578243707 := by
  unfold tailWord_7494983
  simp only [CollatzResearch.WordTrace]
  refine ⟨273364487805964107032225603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182242991870642738021483735 273364487805964107032225603)
  ·
    refine ⟨410046731708946160548338405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273364487805964107032225603 410046731708946160548338405)
    ·
      refine ⟨76883762195427405102813451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410046731708946160548338405 76883762195427405102813451)
      ·
        refine ⟨115325643293141107654220177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76883762195427405102813451 115325643293141107654220177)
        ·
          refine ⟨86494232469855830740665133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115325643293141107654220177 86494232469855830740665133)
          ·
            refine ⟨32435337176195936527749425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86494232469855830740665133 32435337176195936527749425)
            ·
              refine ⟨24326502882146952395812069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32435337176195936527749425 24326502882146952395812069)
              ·
                refine ⟨4561219290402553574214763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24326502882146952395812069 4561219290402553574214763)
                ·
                  refine ⟨6841828935603830361322145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561219290402553574214763 6841828935603830361322145)
                  ·
                    refine ⟨5131371701702872770991609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6841828935603830361322145 5131371701702872770991609)
                    ·
                      refine ⟨3848528776277154578243707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131371701702872770991609 3848528776277154578243707)
                      ·
                        rfl

theorem cell23_7494983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_7494983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494983 prefixEnd_7494983 := by exact prefixLift 7494983
  have htrace : WordTrace (prefixWord ++ tailWord_7494983) baseStart_7494983 baseEnd_7494983 := by
    simpa [prefixWord, tailWord_7494983, baseEnd_7494983] using wordTrace_append hprefix tailTrace_7494983
  have hstable : (prefixWord ++ tailWord_7494983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494983).length < 2 ^ (prefixWord ++ tailWord_7494983).sum := by decide
  have hdescent : baseEnd_7494983 < baseStart_7494983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494985 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_7494985 : Nat := 118140960795 + 7494985 * 2 ^ 59
def prefixEnd_7494985 : Nat := 4983230072969 + 3 ^ 40 * 7494985 * 2
def baseEnd_7494985 : Nat := 1282843267746154523472899

theorem tailTrace_7494985 : CollatzResearch.WordTrace tailWord_7494985 prefixEnd_7494985 1282843267746154523472899 := by
  unfold tailWord_7494985
  simp only [CollatzResearch.WordTrace]
  refine ⟨273364560751956861373798409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182243040501304574249198939 273364560751956861373798409)
  ·
    refine ⟨205023420563967646030348807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273364560751956861373798409 205023420563967646030348807)
    ·
      refine ⟨307535130845951469045523211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205023420563967646030348807 307535130845951469045523211)
      ·
        refine ⟨461302696268927203568284817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307535130845951469045523211 461302696268927203568284817)
        ·
          refine ⟨345977022201695402676213613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461302696268927203568284817 345977022201695402676213613)
          ·
            refine ⟨129741383325635776003580105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345977022201695402676213613 129741383325635776003580105)
            ·
              refine ⟨97306037494226832002685079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129741383325635776003580105 97306037494226832002685079)
              ·
                refine ⟨145959056241340248004027619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97306037494226832002685079 145959056241340248004027619)
                ·
                  refine ⟨218938584362010372006041429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145959056241340248004027619 218938584362010372006041429)
                  ·
                    refine ⟨1282843267746154523472899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218938584362010372006041429 1282843267746154523472899)
                    ·
                      rfl

theorem cell23_7494985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_7494985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494985 prefixEnd_7494985 := by exact prefixLift 7494985
  have htrace : WordTrace (prefixWord ++ tailWord_7494985) baseStart_7494985 baseEnd_7494985 := by
    simpa [prefixWord, tailWord_7494985, baseEnd_7494985] using wordTrace_append hprefix tailTrace_7494985
  have hstable : (prefixWord ++ tailWord_7494985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494985).length < 2 ^ (prefixWord ++ tailWord_7494985).sum := by decide
  have hdescent : baseEnd_7494985 < baseStart_7494985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7494999 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_7494999 : Nat := 118140960795 + 7494999 * 2 ^ 59
def prefixEnd_7494999 : Nat := 4983230072969 + 3 ^ 40 * 7494999 * 2
def baseEnd_7494999 : Nat := 3848536991967626515643633

theorem tailTrace_7494999 : CollatzResearch.WordTrace tailWord_7494999 prefixEnd_7494999 3848536991967626515643633 := by
  unfold tailWord_7494999
  simp only [CollatzResearch.WordTrace]
  refine ⟨273365071373906141764808051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182243380915937427843205367 273365071373906141764808051)
  ·
    refine ⟨410047607060859212647212077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273365071373906141764808051 410047607060859212647212077)
    ·
      refine ⟨153767852647822204742704529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410047607060859212647212077 153767852647822204742704529)
      ·
        refine ⟨115325889485866653557028397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153767852647822204742704529 115325889485866653557028397)
        ·
          refine ⟨43247208557199995083885649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115325889485866653557028397 43247208557199995083885649)
          ·
            refine ⟨32435406417899996312914237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43247208557199995083885649 32435406417899996312914237)
            ·
              refine ⟨12163277406712498617342839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32435406417899996312914237 12163277406712498617342839)
              ·
                refine ⟨18244916110068747926014259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12163277406712498617342839 18244916110068747926014259)
                ·
                  refine ⟨27367374165103121889021389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18244916110068747926014259 27367374165103121889021389)
                  ·
                    refine ⟨10262765311913670708383021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27367374165103121889021389 10262765311913670708383021)
                    ·
                      refine ⟨3848536991967626515643633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10262765311913670708383021 3848536991967626515643633)
                      ·
                        rfl

theorem cell23_7494999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_7494999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7494999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7494999 prefixEnd_7494999 := by exact prefixLift 7494999
  have htrace : WordTrace (prefixWord ++ tailWord_7494999) baseStart_7494999 baseEnd_7494999 := by
    simpa [prefixWord, tailWord_7494999, baseEnd_7494999] using wordTrace_append hprefix tailTrace_7494999
  have hstable : (prefixWord ++ tailWord_7494999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7494999).length < 2 ^ (prefixWord ++ tailWord_7494999).sum := by decide
  have hdescent : baseEnd_7494999 < baseStart_7494999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7494999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495009 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_7495009 : Nat := 118140960795 + 7495009 * 2 ^ 59
def prefixEnd_7495009 : Nat := 4983230072969 + 3 ^ 40 * 7495009 * 2
def baseEnd_7495009 : Nat := 3848542126774171476518587

theorem tailTrace_7495009 : CollatzResearch.WordTrace tailWord_7495009 prefixEnd_7495009 3848542126774171476518587 := by
  unfold tailWord_7495009
  simp only [CollatzResearch.WordTrace]
  refine ⟨273365436103869913472672081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182243624069246608981781387 273365436103869913472672081)
  ·
    refine ⟨205024077077902435104504061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273365436103869913472672081 205024077077902435104504061)
    ·
      refine ⟨76884028904213413164189023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205024077077902435104504061 76884028904213413164189023)
      ·
        refine ⟨115326043356320119746283535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76884028904213413164189023 115326043356320119746283535)
        ·
          refine ⟨172989065034480179619425303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115326043356320119746283535 172989065034480179619425303)
          ·
            refine ⟨259483597551720269429137955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172989065034480179619425303 259483597551720269429137955)
            ·
              refine ⟨389225396327580404143706933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259483597551720269429137955 389225396327580404143706933)
              ·
                refine ⟨36489880905710662888472525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389225396327580404143706933 36489880905710662888472525)
                ·
                  refine ⟨13683705339641498583177197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36489880905710662888472525 13683705339641498583177197)
                  ·
                    refine ⟨5131389502365561968691449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13683705339641498583177197 5131389502365561968691449)
                    ·
                      refine ⟨3848542126774171476518587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131389502365561968691449 3848542126774171476518587)
                      ·
                        rfl

theorem cell23_7495009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_7495009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495009 prefixEnd_7495009 := by exact prefixLift 7495009
  have htrace : WordTrace (prefixWord ++ tailWord_7495009) baseStart_7495009 baseEnd_7495009 := by
    simpa [prefixWord, tailWord_7495009, baseEnd_7495009] using wordTrace_append hprefix tailTrace_7495009
  have hstable : (prefixWord ++ tailWord_7495009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495009).length < 2 ^ (prefixWord ++ tailWord_7495009).sum := by decide
  have hdescent : baseEnd_7495009 < baseStart_7495009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495012 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_7495012 : Nat := 118140960795 + 7495012 * 2 ^ 59
def prefixEnd_7495012 : Nat := 4983230072969 + 3 ^ 40 * 7495012 * 2
def baseEnd_7495012 : Nat := 3848543667216134964781073

theorem tailTrace_7495012 : CollatzResearch.WordTrace tailWord_7495012 prefixEnd_7495012 3848543667216134964781073 := by
  unfold tailWord_7495012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136682772761429522492515645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182243697015239363323354193 136682772761429522492515645)
  ·
    refine ⟨51256039785536070934693367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136682772761429522492515645 51256039785536070934693367)
    ·
      refine ⟨76884059678304106402040051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51256039785536070934693367 76884059678304106402040051)
      ·
        refine ⟨115326089517456159603060077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76884059678304106402040051 115326089517456159603060077)
        ·
          refine ⟨43247283569046059851147529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115326089517456159603060077 43247283569046059851147529)
          ·
            refine ⟨32435462676784544888360647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43247283569046059851147529 32435462676784544888360647)
            ·
              refine ⟨48653194015176817332540971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32435462676784544888360647 48653194015176817332540971)
              ·
                refine ⟨72979791022765225998811457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48653194015176817332540971 72979791022765225998811457)
                ·
                  refine ⟨54734843267073919499108593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72979791022765225998811457 54734843267073919499108593)
                  ·
                    refine ⟨41051132450305439624331445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54734843267073919499108593 41051132450305439624331445)
                    ·
                      refine ⟨3848543667216134964781073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41051132450305439624331445 3848543667216134964781073)
                      ·
                        rfl

theorem cell23_7495012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_7495012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495012 prefixEnd_7495012 := by exact prefixLift 7495012
  have htrace : WordTrace (prefixWord ++ tailWord_7495012) baseStart_7495012 baseEnd_7495012 := by
    simpa [prefixWord, tailWord_7495012, baseEnd_7495012] using wordTrace_append hprefix tailTrace_7495012
  have hstable : (prefixWord ++ tailWord_7495012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495012).length < 2 ^ (prefixWord ++ tailWord_7495012).sum := by decide
  have hdescent : baseEnd_7495012 < baseStart_7495012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495026 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_7495026 : Nat := 118140960795 + 7495026 * 2 ^ 59
def prefixEnd_7495026 : Nat := 4983230072969 + 3 ^ 40 * 7495026 * 2
def baseEnd_7495026 : Nat := 3848550855945297910006009

theorem tailTrace_7495026 : CollatzResearch.WordTrace tailWord_7495026 prefixEnd_7495026 3848550855945297910006009 := by
  unfold tailWord_7495026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68341514036202081344010233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182244037429872216917360621 68341514036202081344010233)
  ·
    refine ⟨51256135527151561008007675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68341514036202081344010233 51256135527151561008007675)
    ·
      refine ⟨76884203290727341512011513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51256135527151561008007675 76884203290727341512011513)
      ·
        refine ⟨57663152468045506134008635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76884203290727341512011513 57663152468045506134008635)
        ·
          refine ⟨86494728702068259201012953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57663152468045506134008635 86494728702068259201012953)
          ·
            refine ⟨64871046526551194400759715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86494728702068259201012953 64871046526551194400759715)
            ·
              refine ⟨97306569789826791601139573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64871046526551194400759715 97306569789826791601139573)
              ·
                refine ⟨9122490917796261712606835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97306569789826791601139573 9122490917796261712606835)
                ·
                  refine ⟨13683736376694392568910253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9122490917796261712606835 13683736376694392568910253)
                  ·
                    refine ⟨5131401141260397213341345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13683736376694392568910253 5131401141260397213341345)
                    ·
                      refine ⟨3848550855945297910006009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131401141260397213341345 3848550855945297910006009)
                      ·
                        rfl

theorem cell23_7495026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_7495026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495026 prefixEnd_7495026 := by exact prefixLift 7495026
  have htrace : WordTrace (prefixWord ++ tailWord_7495026) baseStart_7495026 baseEnd_7495026 := by
    simpa [prefixWord, tailWord_7495026, baseEnd_7495026] using wordTrace_append hprefix tailTrace_7495026
  have hstable : (prefixWord ++ tailWord_7495026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495026).length < 2 ^ (prefixWord ++ tailWord_7495026).sum := by decide
  have hdescent : baseEnd_7495026 < baseStart_7495026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495052 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7495052 : Nat := 118140960795 + 7495052 * 2 ^ 59
def prefixEnd_7495052 : Nat := 4983230072969 + 3 ^ 40 * 7495052 * 2
def baseEnd_7495052 : Nat := 3848564206442314808280889

theorem tailTrace_7495052 : CollatzResearch.WordTrace tailWord_7495052 prefixEnd_7495052 3848564206442314808280889 := by
  unfold tailWord_7495052
  simp only [CollatzResearch.WordTrace]
  refine ⟨136683502221357065908243705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182244669628476087877658273 136683502221357065908243705)
  ·
    refine ⟨102512626666017799431182779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136683502221357065908243705 102512626666017799431182779)
    ·
      refine ⟨153768939999026699146774169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102512626666017799431182779 153768939999026699146774169)
      ·
        refine ⟨115326704999270024360080627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153768939999026699146774169 115326704999270024360080627)
        ·
          refine ⟨172990057498905036540120941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115326704999270024360080627 172990057498905036540120941)
          ·
            refine ⟨64871271562089388702545353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172990057498905036540120941 64871271562089388702545353)
            ·
              refine ⟨48653453671567041526909015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64871271562089388702545353 48653453671567041526909015)
              ·
                refine ⟨72980180507350562290363523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48653453671567041526909015 72980180507350562290363523)
                ·
                  refine ⟨109470270761025843435545285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72980180507350562290363523 109470270761025843435545285)
                  ·
                    refine ⟨20525675767692345644164741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109470270761025843435545285 20525675767692345644164741)
                    ·
                      refine ⟨3848564206442314808280889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20525675767692345644164741 3848564206442314808280889)
                      ·
                        rfl

theorem cell23_7495052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7495052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495052 prefixEnd_7495052 := by exact prefixLift 7495052
  have htrace : WordTrace (prefixWord ++ tailWord_7495052) baseStart_7495052 baseEnd_7495052 := by
    simpa [prefixWord, tailWord_7495052, baseEnd_7495052] using wordTrace_append hprefix tailTrace_7495052
  have hstable : (prefixWord ++ tailWord_7495052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495052).length < 2 ^ (prefixWord ++ tailWord_7495052).sum := by decide
  have hdescent : baseEnd_7495052 < baseStart_7495052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495060 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7495060 : Nat := 118140960795 + 7495060 * 2 ^ 59
def prefixEnd_7495060 : Nat := 4983230072969 + 3 ^ 40 * 7495060 * 2
def baseEnd_7495060 : Nat := 3848568314287550776980853

theorem tailTrace_7495060 : CollatzResearch.WordTrace tailWord_7495060 prefixEnd_7495060 3848568314287550776980853 := by
  unfold tailWord_7495060
  simp only [CollatzResearch.WordTrace]
  refine ⟨136683648113342574591389317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182244864151123432788519089 136683648113342574591389317)
  ·
    refine ⟨25628184021251732735885497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136683648113342574591389317 25628184021251732735885497)
    ·
      refine ⟨19221138015938799551914123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25628184021251732735885497 19221138015938799551914123)
      ·
        refine ⟨28831707023908199327871185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19221138015938799551914123 28831707023908199327871185)
        ·
          refine ⟨21623780267931149495903389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28831707023908199327871185 21623780267931149495903389)
          ·
            refine ⟨8108917600474181060963771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21623780267931149495903389 8108917600474181060963771)
            ·
              refine ⟨12163376400711271591445657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108917600474181060963771 12163376400711271591445657)
              ·
                refine ⟨9122532300533453693584243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12163376400711271591445657 9122532300533453693584243)
                ·
                  refine ⟨13683798450800180540376365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9122532300533453693584243 13683798450800180540376365)
                  ·
                    refine ⟨5131424419050067702641137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13683798450800180540376365 5131424419050067702641137)
                    ·
                      refine ⟨3848568314287550776980853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131424419050067702641137 3848568314287550776980853)
                      ·
                        rfl

theorem cell23_7495060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7495060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495060 prefixEnd_7495060 := by exact prefixLift 7495060
  have htrace : WordTrace (prefixWord ++ tailWord_7495060) baseStart_7495060 baseEnd_7495060 := by
    simpa [prefixWord, tailWord_7495060, baseEnd_7495060] using wordTrace_append hprefix tailTrace_7495060
  have hstable : (prefixWord ++ tailWord_7495060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495060).length < 2 ^ (prefixWord ++ tailWord_7495060).sum := by decide
  have hdescent : baseEnd_7495060 < baseStart_7495060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495089 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7495089 : Nat := 118140960795 + 7495089 * 2 ^ 59
def prefixEnd_7495089 : Nat := 4983230072969 + 3 ^ 40 * 7495089 * 2
def baseEnd_7495089 : Nat := 3848583205226531163518219

theorem tailTrace_7495089 : CollatzResearch.WordTrace tailWord_7495089 prefixEnd_7495089 3848583205226531163518219 := by
  unfold tailWord_7495089
  simp only [CollatzResearch.WordTrace]
  refine ⟨273368353943580087135584321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182245569295720058090389547 273368353943580087135584321)
  ·
    refine ⟨205026265457685065351688241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273368353943580087135584321 205026265457685065351688241)
    ·
      refine ⟨153769699093263799013766181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205026265457685065351688241 153769699093263799013766181)
      ·
        refine ⟨28831818579986962315081159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153769699093263799013766181 28831818579986962315081159)
        ·
          refine ⟨43247727869980443472621739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28831818579986962315081159 43247727869980443472621739)
          ·
            refine ⟨64871591804970665208932609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43247727869980443472621739 64871591804970665208932609)
            ·
              refine ⟨48653693853727998906699457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64871591804970665208932609 48653693853727998906699457)
              ·
                refine ⟨36490270390295999180024593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48653693853727998906699457 36490270390295999180024593)
                ·
                  refine ⟨27367702792721999385018445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36490270390295999180024593 27367702792721999385018445)
                  ·
                    refine ⟨10262888547270749769381917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27367702792721999385018445 10262888547270749769381917)
                    ·
                      refine ⟨3848583205226531163518219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10262888547270749769381917 3848583205226531163518219)
                      ·
                        rfl

theorem cell23_7495089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7495089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495089 prefixEnd_7495089 := by exact prefixLift 7495089
  have htrace : WordTrace (prefixWord ++ tailWord_7495089) baseStart_7495089 baseEnd_7495089 := by
    simpa [prefixWord, tailWord_7495089, baseEnd_7495089] using wordTrace_append hprefix tailTrace_7495089
  have hstable : (prefixWord ++ tailWord_7495089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495089).length < 2 ^ (prefixWord ++ tailWord_7495089).sum := by decide
  have hdescent : baseEnd_7495089 < baseStart_7495089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495096 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 5]
def baseStart_7495096 : Nat := 118140960795 + 7495096 * 2 ^ 59
def prefixEnd_7495096 : Nat := 4983230072969 + 3 ^ 40 * 7495096 * 2
def baseEnd_7495096 : Nat := 427620755510123626236743

theorem tailTrace_7495096 : CollatzResearch.WordTrace tailWord_7495096 prefixEnd_7495096 427620755510123626236743 := by
  unfold tailWord_7495096
  simp only [CollatzResearch.WordTrace]
  refine ⟨136684304627277363665544571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182245739503036484887392761 136684304627277363665544571)
  ·
    refine ⟨205026456940916045498316857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136684304627277363665544571 205026456940916045498316857)
    ·
      refine ⟨153769842705687034123737643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205026456940916045498316857 153769842705687034123737643)
      ·
        refine ⟨230654764058530551185606465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153769842705687034123737643 230654764058530551185606465)
        ·
          refine ⟨172991073043897913389204849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230654764058530551185606465 172991073043897913389204849)
          ·
            refine ⟨129743304782923435041903637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172991073043897913389204849 129743304782923435041903637)
            ·
              refine ⟨6081717411699536017589233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129743304782923435041903637 6081717411699536017589233)
              ·
                refine ⟨4561288058774652013191925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081717411699536017589233 4561288058774652013191925)
                ·
                  refine ⟨427620755510123626236743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561288058774652013191925 427620755510123626236743)
                  ·
                    rfl

theorem cell23_7495096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 5].length) (baseStart_7495096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495096 prefixEnd_7495096 := by exact prefixLift 7495096
  have htrace : WordTrace (prefixWord ++ tailWord_7495096) baseStart_7495096 baseEnd_7495096 := by
    simpa [prefixWord, tailWord_7495096, baseEnd_7495096] using wordTrace_append hprefix tailTrace_7495096
  have hstable : (prefixWord ++ tailWord_7495096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495096).length < 2 ^ (prefixWord ++ tailWord_7495096).sum := by decide
  have hdescent : baseEnd_7495096 < baseStart_7495096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495126 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7495126 : Nat := 118140960795 + 7495126 * 2 ^ 59
def prefixEnd_7495126 : Nat := 4983230072969 + 3 ^ 40 * 7495126 * 2
def baseEnd_7495126 : Nat := 1282867401336915839585183

theorem tailTrace_7495126 : CollatzResearch.WordTrace tailWord_7495126 prefixEnd_7495126 1282867401336915839585183 := by
  unfold tailWord_7495126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085606465277877653417577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182246468962964028303120821 17085606465277877653417577)
  ·
    refine ⟨12814204848958408240063183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17085606465277877653417577 12814204848958408240063183)
    ·
      refine ⟨19221307273437612360094775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12814204848958408240063183 19221307273437612360094775)
      ·
        refine ⟨28831960910156418540142163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19221307273437612360094775 28831960910156418540142163)
        ·
          refine ⟨43247941365234627810213245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28831960910156418540142163 43247941365234627810213245)
          ·
            refine ⟨16217978011962985428829967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43247941365234627810213245 16217978011962985428829967)
            ·
              refine ⟨24326967017944478143244951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16217978011962985428829967 24326967017944478143244951)
              ·
                refine ⟨36490450526916717214867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24326967017944478143244951 36490450526916717214867427)
                ·
                  refine ⟨54735675790375075822301141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36490450526916717214867427 54735675790375075822301141)
                  ·
                    refine ⟨1282867401336915839585183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54735675790375075822301141 1282867401336915839585183)
                    ·
                      rfl

theorem cell23_7495126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7495126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495126 prefixEnd_7495126 := by exact prefixLift 7495126
  have htrace : WordTrace (prefixWord ++ tailWord_7495126) baseStart_7495126 baseEnd_7495126 := by
    simpa [prefixWord, tailWord_7495126, baseEnd_7495126] using wordTrace_append hprefix tailTrace_7495126
  have hstable : (prefixWord ++ tailWord_7495126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495126).length < 2 ^ (prefixWord ++ tailWord_7495126).sum := by decide
  have hdescent : baseEnd_7495126 < baseStart_7495126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495129 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_7495129 : Nat := 118140960795 + 7495129 * 2 ^ 59
def prefixEnd_7495129 : Nat := 4983230072969 + 3 ^ 40 * 7495129 * 2
def baseEnd_7495129 : Nat := 3848603744452711007018035

theorem tailTrace_7495129 : CollatzResearch.WordTrace tailWord_7495129 prefixEnd_7495129 3848603744452711007018035 := by
  unfold tailWord_7495129
  simp only [CollatzResearch.WordTrace]
  refine ⟨273369812863435173967040441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182246541908956782644693627 273369812863435173967040441)
  ·
    refine ⟨205027359647576380475280331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273369812863435173967040441 205027359647576380475280331)
    ·
      refine ⟨307541039471364570712920497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205027359647576380475280331 307541039471364570712920497)
      ·
        refine ⟨230655779603523428034690373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307541039471364570712920497 230655779603523428034690373)
        ·
          refine ⟨43247958675660642756504445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230655779603523428034690373 43247958675660642756504445)
          ·
            refine ⟨16217984503372741033689167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43247958675660642756504445 16217984503372741033689167)
            ·
              refine ⟨24326976755059111550533751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16217984503372741033689167 24326976755059111550533751)
              ·
                refine ⟨36490465132588667325800627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24326976755059111550533751 36490465132588667325800627)
                ·
                  refine ⟨54735697698883000988700941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36490465132588667325800627 54735697698883000988700941)
                  ·
                    refine ⟨20525886637081125370762853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54735697698883000988700941 20525886637081125370762853)
                    ·
                      refine ⟨3848603744452711007018035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20525886637081125370762853 3848603744452711007018035)
                      ·
                        rfl

theorem cell23_7495129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_7495129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495129 prefixEnd_7495129 := by exact prefixLift 7495129
  have htrace : WordTrace (prefixWord ++ tailWord_7495129) baseStart_7495129 baseEnd_7495129 := by
    simpa [prefixWord, tailWord_7495129, baseEnd_7495129] using wordTrace_append hprefix tailTrace_7495129
  have hstable : (prefixWord ++ tailWord_7495129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495129).length < 2 ^ (prefixWord ++ tailWord_7495129).sum := by decide
  have hdescent : baseEnd_7495129 < baseStart_7495129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495289 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_7495289 : Nat := 118140960795 + 7495289 * 2 ^ 59
def prefixEnd_7495289 : Nat := 4983230072969 + 3 ^ 40 * 7495289 * 2
def baseEnd_7495289 : Nat := 1282895300452476793672433

theorem tailTrace_7495289 : CollatzResearch.WordTrace tailWord_7495289 prefixEnd_7495289 1282895300452476793672433 := by
  unfold tailWord_7495289
  simp only [CollatzResearch.WordTrace]
  refine ⟨273375648542855521292864921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182250432361903680861909947 273375648542855521292864921)
  ·
    refine ⟨205031736407141640969648691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273375648542855521292864921 205031736407141640969648691)
    ·
      refine ⟨307547604610712461454473037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205031736407141640969648691 307547604610712461454473037)
      ·
        refine ⟨115330351729017173045427389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307547604610712461454473037 115330351729017173045427389)
        ·
          refine ⟨43248881898381439892035271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115330351729017173045427389 43248881898381439892035271)
          ·
            refine ⟨64873322847572159838052907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43248881898381439892035271 64873322847572159838052907)
            ·
              refine ⟨97309984271358239757079361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64873322847572159838052907 97309984271358239757079361)
              ·
                refine ⟨72982488203518679817809521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97309984271358239757079361 72982488203518679817809521)
                ·
                  refine ⟨54736866152639009863357141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72982488203518679817809521 54736866152639009863357141)
                  ·
                    refine ⟨1282895300452476793672433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54736866152639009863357141 1282895300452476793672433)
                    ·
                      rfl

theorem cell23_7495289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_7495289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495289 prefixEnd_7495289 := by exact prefixLift 7495289
  have htrace : WordTrace (prefixWord ++ tailWord_7495289) baseStart_7495289 baseEnd_7495289 := by
    simpa [prefixWord, tailWord_7495289, baseEnd_7495289] using wordTrace_append hprefix tailTrace_7495289
  have hstable : (prefixWord ++ tailWord_7495289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495289).length < 2 ^ (prefixWord ++ tailWord_7495289).sum := by decide
  have hdescent : baseEnd_7495289 < baseStart_7495289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495299 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_7495299 : Nat := 118140960795 + 7495299 * 2 ^ 59
def prefixEnd_7495299 : Nat := 4983230072969 + 3 ^ 40 * 7495299 * 2
def baseEnd_7495299 : Nat := 3848691036163975341892253

theorem tailTrace_7495299 : CollatzResearch.WordTrace tailWord_7495299 prefixEnd_7495299 3848691036163975341892253 := by
  unfold tailWord_7495299
  simp only [CollatzResearch.WordTrace]
  refine ⟨273376013272819293000728951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182250675515212862000485967 273376013272819293000728951)
  ·
    refine ⟨410064019909228939501093427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273376013272819293000728951 410064019909228939501093427)
    ·
      refine ⟨615096029863843409251640141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410064019909228939501093427 615096029863843409251640141)
      ·
        refine ⟨230661011198941278469365053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615096029863843409251640141 230661011198941278469365053)
        ·
          refine ⟨86497879199602979426011895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230661011198941278469365053 86497879199602979426011895)
          ·
            refine ⟨129746818799404469139017843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86497879199602979426011895 129746818799404469139017843)
            ·
              refine ⟨194620228199106703708526765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129746818799404469139017843 194620228199106703708526765)
              ·
                refine ⟨72982585574665013890697537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194620228199106703708526765 72982585574665013890697537)
                ·
                  refine ⟨54736939180998760418023153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72982585574665013890697537 54736939180998760418023153)
                  ·
                    refine ⟨41052704385749070313517365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54736939180998760418023153 41052704385749070313517365)
                    ·
                      refine ⟨3848691036163975341892253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41052704385749070313517365 3848691036163975341892253)
                      ·
                        rfl

theorem cell23_7495299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_7495299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495299 prefixEnd_7495299 := by exact prefixLift 7495299
  have htrace : WordTrace (prefixWord ++ tailWord_7495299) baseStart_7495299 baseEnd_7495299 := by
    simpa [prefixWord, tailWord_7495299, baseEnd_7495299] using wordTrace_append hprefix tailTrace_7495299
  have hstable : (prefixWord ++ tailWord_7495299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495299).length < 2 ^ (prefixWord ++ tailWord_7495299).sum := by decide
  have hdescent : baseEnd_7495299 < baseStart_7495299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495304 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7495304 : Nat := 118140960795 + 7495304 * 2 ^ 59
def prefixEnd_7495304 : Nat := 4983230072969 + 3 ^ 40 * 7495304 * 2
def baseEnd_7495304 : Nat := 3848693603567247822329731

theorem tailTrace_7495304 : CollatzResearch.WordTrace tailWord_7495304 prefixEnd_7495304 3848693603567247822329731 := by
  unfold tailWord_7495304
  simp only [CollatzResearch.WordTrace]
  refine ⟨136688097818900589427330483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182250797091867452569773977 136688097818900589427330483)
  ·
    refine ⟨205032146728350884140995725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136688097818900589427330483 205032146728350884140995725)
    ·
      refine ⟨76887055023131581552873397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205032146728350884140995725 76887055023131581552873397)
      ·
        refine ⟨7208161408418585770581881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76887055023131581552873397 7208161408418585770581881)
        ·
          refine ⟨5406121056313939327936411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208161408418585770581881 5406121056313939327936411)
          ·
            refine ⟨8109181584470908991904617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406121056313939327936411 8109181584470908991904617)
            ·
              refine ⟨6081886188353181743928463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109181584470908991904617 6081886188353181743928463)
              ·
                refine ⟨9122829282529772615892695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081886188353181743928463 9122829282529772615892695)
                ·
                  refine ⟨13684243923794658923839043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9122829282529772615892695 13684243923794658923839043)
                  ·
                    refine ⟨20526365885691988385758565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13684243923794658923839043 20526365885691988385758565)
                    ·
                      refine ⟨3848693603567247822329731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20526365885691988385758565 3848693603567247822329731)
                      ·
                        rfl

theorem cell23_7495304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7495304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495304 prefixEnd_7495304 := by exact prefixLift 7495304
  have htrace : WordTrace (prefixWord ++ tailWord_7495304) baseStart_7495304 baseEnd_7495304 := by
    simpa [prefixWord, tailWord_7495304, baseEnd_7495304] using wordTrace_append hprefix tailTrace_7495304
  have hstable : (prefixWord ++ tailWord_7495304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495304).length < 2 ^ (prefixWord ++ tailWord_7495304).sum := by decide
  have hdescent : baseEnd_7495304 < baseStart_7495304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495320 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7495320 : Nat := 118140960795 + 7495320 * 2 ^ 59
def prefixEnd_7495320 : Nat := 4983230072969 + 3 ^ 40 * 7495320 * 2
def baseEnd_7495320 : Nat := 3848701819257719759729657

theorem tailTrace_7495320 : CollatzResearch.WordTrace tailWord_7495320 prefixEnd_7495320 3848701819257719759729657 := by
  unfold tailWord_7495320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136688389602871606793621707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182251186137162142391495609 136688389602871606793621707)
  ·
    refine ⟨205032584404307410190432561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136688389602871606793621707 205032584404307410190432561)
    ·
      refine ⟨153774438303230557642824421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205032584404307410190432561 153774438303230557642824421)
      ·
        refine ⟨28832707181855729558029579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153774438303230557642824421 28832707181855729558029579)
        ·
          refine ⟨43249060772783594337044369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28832707181855729558029579 43249060772783594337044369)
          ·
            refine ⟨32436795579587695752783277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43249060772783594337044369 32436795579587695752783277)
            ·
              refine ⟨12163798342345385907293729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32436795579587695752783277 12163798342345385907293729)
              ·
                refine ⟨9122848756759039430470297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12163798342345385907293729 9122848756759039430470297)
                ·
                  refine ⟨6842136567569279572852723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9122848756759039430470297 6842136567569279572852723)
                  ·
                    refine ⟨10263204851353919359279085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6842136567569279572852723 10263204851353919359279085)
                    ·
                      refine ⟨3848701819257719759729657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263204851353919359279085 3848701819257719759729657)
                      ·
                        rfl

theorem cell23_7495320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7495320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495320 prefixEnd_7495320 := by exact prefixLift 7495320
  have htrace : WordTrace (prefixWord ++ tailWord_7495320) baseStart_7495320 baseEnd_7495320 := by
    simpa [prefixWord, tailWord_7495320, baseEnd_7495320] using wordTrace_append hprefix tailTrace_7495320
  have hstable : (prefixWord ++ tailWord_7495320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495320).length < 2 ^ (prefixWord ++ tailWord_7495320).sum := by decide
  have hdescent : baseEnd_7495320 < baseStart_7495320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495346 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_7495346 : Nat := 118140960795 + 7495346 * 2 ^ 59
def prefixEnd_7495346 : Nat := 4983230072969 + 3 ^ 40 * 7495346 * 2
def baseEnd_7495346 : Nat := 3848715169754736658004537

theorem tailTrace_7495346 : CollatzResearch.WordTrace tailWord_7495346 prefixEnd_7495346 3848715169754736658004537 := by
  unfold tailWord_7495346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68344431875912255006922473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182251818335766013351793261 68344431875912255006922473)
  ·
    refine ⟨51258323906934191255191855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68344431875912255006922473 51258323906934191255191855)
    ·
      refine ⟨76887485860401286882787783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51258323906934191255191855 76887485860401286882787783)
      ·
        refine ⟨115331228790601930324181675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76887485860401286882787783 115331228790601930324181675)
        ·
          refine ⟨172996843185902895486272513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115331228790601930324181675 172996843185902895486272513)
          ·
            refine ⟨129747632389427171614704385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172996843185902895486272513 129747632389427171614704385)
            ·
              refine ⟨97310724292070378711028289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129747632389427171614704385 97310724292070378711028289)
              ·
                refine ⟨72983043219052784033271217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97310724292070378711028289 72983043219052784033271217)
                ·
                  refine ⟨54737282414289588024953413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72983043219052784033271217 54737282414289588024953413)
                  ·
                    refine ⟨10263240452679297754678765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54737282414289588024953413 10263240452679297754678765)
                    ·
                      refine ⟨3848715169754736658004537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263240452679297754678765 3848715169754736658004537)
                      ·
                        rfl

theorem cell23_7495346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_7495346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495346 prefixEnd_7495346 := by exact prefixLift 7495346
  have htrace : WordTrace (prefixWord ++ tailWord_7495346) baseStart_7495346 baseEnd_7495346 := by
    simpa [prefixWord, tailWord_7495346, baseEnd_7495346] using wordTrace_append hprefix tailTrace_7495346
  have hstable : (prefixWord ++ tailWord_7495346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495346).length < 2 ^ (prefixWord ++ tailWord_7495346).sum := by decide
  have hdescent : baseEnd_7495346 < baseStart_7495346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495369 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_7495369 : Nat := 118140960795 + 7495369 * 2 ^ 59
def prefixEnd_7495369 : Nat := 4983230072969 + 3 ^ 40 * 7495369 * 2
def baseEnd_7495369 : Nat := 3848726979809790068016931

theorem tailTrace_7495369 : CollatzResearch.WordTrace tailWord_7495369 prefixEnd_7495369 3848726979809790068016931 := by
  unfold tailWord_7495369
  simp only [CollatzResearch.WordTrace]
  refine ⟨273378566382565694955777161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182252377588377129970518107 273378566382565694955777161)
  ·
    refine ⟨205033924786924271216832871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273378566382565694955777161 205033924786924271216832871)
    ·
      refine ⟨307550887180386406825249307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205033924786924271216832871 307550887180386406825249307)
      ·
        refine ⟨461326330770579610237873961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307550887180386406825249307 461326330770579610237873961)
        ·
          refine ⟨345994748077934707678405471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461326330770579610237873961 345994748077934707678405471)
          ·
            refine ⟨518992122116902061517608207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345994748077934707678405471 518992122116902061517608207)
            ·
              refine ⟨778488183175353092276412311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518992122116902061517608207 778488183175353092276412311)
              ·
                refine ⟨1167732274763029638414618467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778488183175353092276412311 1167732274763029638414618467)
                ·
                  refine ⟨1751598412144544457621927701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167732274763029638414618467 1751598412144544457621927701)
                  ·
                    refine ⟨82106175569275521451027861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1751598412144544457621927701 82106175569275521451027861)
                    ·
                      refine ⟨3848726979809790068016931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82106175569275521451027861 3848726979809790068016931)
                      ·
                        rfl

theorem cell23_7495369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_7495369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495369 prefixEnd_7495369 := by exact prefixLift 7495369
  have htrace : WordTrace (prefixWord ++ tailWord_7495369) baseStart_7495369 baseEnd_7495369 := by
    simpa [prefixWord, tailWord_7495369, baseEnd_7495369] using wordTrace_append hprefix tailTrace_7495369
  have hstable : (prefixWord ++ tailWord_7495369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495369).length < 2 ^ (prefixWord ++ tailWord_7495369).sum := by decide
  have hdescent : baseEnd_7495369 < baseStart_7495369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495376 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_7495376 : Nat := 118140960795 + 7495376 * 2 ^ 59
def prefixEnd_7495376 : Nat := 4983230072969 + 3 ^ 40 * 7495376 * 2
def baseEnd_7495376 : Nat := 3848730574174371540629399

theorem tailTrace_7495376 : CollatzResearch.WordTrace tailWord_7495376 prefixEnd_7495376 3848730574174371540629399 := by
  unfold tailWord_7495376
  simp only [CollatzResearch.WordTrace]
  refine ⟨136689410846770167575640991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182252547795693556767521321 136689410846770167575640991)
  ·
    refine ⟨205034116270155251363461487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136689410846770167575640991 205034116270155251363461487)
    ·
      refine ⟨307551174405232877045192231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205034116270155251363461487 307551174405232877045192231)
      ·
        refine ⟨461326761607849315567788347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307551174405232877045192231 461326761607849315567788347)
        ·
          refine ⟨691990142411773973351682521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461326761607849315567788347 691990142411773973351682521)
          ·
            refine ⟨518992606808830480013761891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691990142411773973351682521 518992606808830480013761891)
            ·
              refine ⟨778488910213245720020642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518992606808830480013761891 778488910213245720020642837)
              ·
                refine ⟨36491667666245893125967633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 778488910213245720020642837 36491667666245893125967633)
                ·
                  refine ⟨27368750749684419844475725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36491667666245893125967633 27368750749684419844475725)
                  ·
                    refine ⟨10263281531131657441678397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27368750749684419844475725 10263281531131657441678397)
                    ·
                      refine ⟨3848730574174371540629399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263281531131657441678397 3848730574174371540629399)
                      ·
                        rfl

theorem cell23_7495376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_7495376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495376 prefixEnd_7495376 := by exact prefixLift 7495376
  have htrace : WordTrace (prefixWord ++ tailWord_7495376) baseStart_7495376 baseEnd_7495376 := by
    simpa [prefixWord, tailWord_7495376, baseEnd_7495376] using wordTrace_append hprefix tailTrace_7495376
  have hstable : (prefixWord ++ tailWord_7495376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495376).length < 2 ^ (prefixWord ++ tailWord_7495376).sum := by decide
  have hdescent : baseEnd_7495376 < baseStart_7495376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495396 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_7495396 : Nat := 118140960795 + 7495396 * 2 ^ 59
def prefixEnd_7495396 : Nat := 4983230072969 + 3 ^ 40 * 7495396 * 2
def baseEnd_7495396 : Nat := 1282913614595820487459769

theorem tailTrace_7495396 : CollatzResearch.WordTrace tailWord_7495396 prefixEnd_7495396 1282913614595820487459769 := by
  unfold tailWord_7495396
  simp only [CollatzResearch.WordTrace]
  refine ⟨136689775576733939283505021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182253034102311919044673361 136689775576733939283505021)
  ·
    refine ⟨51258665841275227231314383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136689775576733939283505021 51258665841275227231314383)
    ·
      refine ⟨76887998761912840846971575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51258665841275227231314383 76887998761912840846971575)
      ·
        refine ⟨115331998142869261270457363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76887998761912840846971575 115331998142869261270457363)
        ·
          refine ⟨172997997214303891905686045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115331998142869261270457363 172997997214303891905686045)
          ·
            refine ⟨64874248955363959464632267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172997997214303891905686045 64874248955363959464632267)
            ·
              refine ⟨97311373433045939196948401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64874248955363959464632267 97311373433045939196948401)
              ·
                refine ⟨72983530074784454397711301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97311373433045939196948401 72983530074784454397711301)
                ·
                  refine ⟨13684411889022085199570869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72983530074784454397711301 13684411889022085199570869)
                  ·
                    refine ⟨1282913614595820487459769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13684411889022085199570869 1282913614595820487459769)
                    ·
                      rfl

theorem cell23_7495396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_7495396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495396 prefixEnd_7495396 := by exact prefixLift 7495396
  have htrace : WordTrace (prefixWord ++ tailWord_7495396) baseStart_7495396 baseEnd_7495396 := by
    simpa [prefixWord, tailWord_7495396, baseEnd_7495396] using wordTrace_append hprefix tailTrace_7495396
  have hstable : (prefixWord ++ tailWord_7495396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495396).length < 2 ^ (prefixWord ++ tailWord_7495396).sum := by decide
  have hdescent : baseEnd_7495396 < baseStart_7495396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495406 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7495406 : Nat := 118140960795 + 7495406 * 2 ^ 59
def prefixEnd_7495406 : Nat := 4983230072969 + 3 ^ 40 * 7495406 * 2
def baseEnd_7495406 : Nat := 3848745978594006423254261

theorem tailTrace_7495406 : CollatzResearch.WordTrace tailWord_7495406 prefixEnd_7495406 3848745978594006423254261 := by
  unfold tailWord_7495406
  simp only [CollatzResearch.WordTrace]
  refine ⟨34172489485428956284359259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182253277255621100183249381 34172489485428956284359259)
  ·
    refine ⟨51258734228143434426538889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34172489485428956284359259 51258734228143434426538889)
    ·
      refine ⟨38444050671107575819904167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51258734228143434426538889 38444050671107575819904167)
      ·
        refine ⟨57666076006661363729856251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38444050671107575819904167 57666076006661363729856251)
        ·
          refine ⟨86499114009992045594784377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57666076006661363729856251 86499114009992045594784377)
          ·
            refine ⟨64874335507494034196088283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86499114009992045594784377 64874335507494034196088283)
            ·
              refine ⟨97311503261241051294132425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64874335507494034196088283 97311503261241051294132425)
              ·
                refine ⟨72983627445930788470599319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97311503261241051294132425 72983627445930788470599319)
                ·
                  refine ⟨109475441168896182705898979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72983627445930788470599319 109475441168896182705898979)
                  ·
                    refine ⟨164213161753344274058848469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109475441168896182705898979 164213161753344274058848469)
                    ·
                      refine ⟨3848745978594006423254261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164213161753344274058848469 3848745978594006423254261)
                      ·
                        rfl

theorem cell23_7495406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7495406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495406 prefixEnd_7495406 := by exact prefixLift 7495406
  have htrace : WordTrace (prefixWord ++ tailWord_7495406) baseStart_7495406 baseEnd_7495406 := by
    simpa [prefixWord, tailWord_7495406, baseEnd_7495406] using wordTrace_append hprefix tailTrace_7495406
  have hstable : (prefixWord ++ tailWord_7495406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495406).length < 2 ^ (prefixWord ++ tailWord_7495406).sum := by decide
  have hdescent : baseEnd_7495406 < baseStart_7495406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495433 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 4, 2]
def baseStart_7495433 : Nat := 118140960795 + 7495433 * 2 ^ 59
def prefixEnd_7495433 : Nat := 4983230072969 + 3 ^ 40 * 7495433 * 2
def baseEnd_7495433 : Nat := 3848759842571677817616637

theorem tailTrace_7495433 : CollatzResearch.WordTrace tailWord_7495433 prefixEnd_7495433 3848759842571677817616637 := by
  unfold tailWord_7495433
  simp only [CollatzResearch.WordTrace]
  refine ⟨273380900654333833886106953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182253933769555889257404635 273380900654333833886106953)
  ·
    refine ⟨205035675490750375414580215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273380900654333833886106953 205035675490750375414580215)
    ·
      refine ⟨307553513236125563121870323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205035675490750375414580215 307553513236125563121870323)
      ·
        refine ⟨461330269854188344682805485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307553513236125563121870323 461330269854188344682805485)
        ·
          refine ⟨172998851195320629256052057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461330269854188344682805485 172998851195320629256052057)
          ·
            refine ⟨129749138396490471942039043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172998851195320629256052057 129749138396490471942039043)
            ·
              refine ⟨194623707594735707913058565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129749138396490471942039043 194623707594735707913058565)
              ·
                refine ⟨36491945174012945233698481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194623707594735707913058565 36491945174012945233698481)
                ·
                  refine ⟨27368958880509708925273861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36491945174012945233698481 27368958880509708925273861)
                  ·
                    refine ⟨5131679790095570423488849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27368958880509708925273861 5131679790095570423488849)
                    ·
                      refine ⟨3848759842571677817616637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131679790095570423488849 3848759842571677817616637)
                      ·
                        rfl

theorem cell23_7495433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4, 2].length) (baseStart_7495433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495433 prefixEnd_7495433 := by exact prefixLift 7495433
  have htrace : WordTrace (prefixWord ++ tailWord_7495433) baseStart_7495433 baseEnd_7495433 := by
    simpa [prefixWord, tailWord_7495433, baseEnd_7495433] using wordTrace_append hprefix tailTrace_7495433
  have hstable : (prefixWord ++ tailWord_7495433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495433).length < 2 ^ (prefixWord ++ tailWord_7495433).sum := by decide
  have hdescent : baseEnd_7495433 < baseStart_7495433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495444 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7495444 : Nat := 118140960795 + 7495444 * 2 ^ 59
def prefixEnd_7495444 : Nat := 4983230072969 + 3 ^ 40 * 7495444 * 2
def baseEnd_7495444 : Nat := 3848765490858877274579087

theorem tailTrace_7495444 : CollatzResearch.WordTrace tailWord_7495444 prefixEnd_7495444 3848765490858877274579087 := by
  unfold tailWord_7495444
  simp only [CollatzResearch.WordTrace]
  refine ⟨136690650928646991382378693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182254201238195988509838257 136690650928646991382378693)
  ·
    refine ⟨25629497049121310884196005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136690650928646991382378693 25629497049121310884196005)
    ·
      refine ⟨4805530696710245790786751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25629497049121310884196005 4805530696710245790786751)
      ·
        refine ⟨7208296045065368686180127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805530696710245790786751 7208296045065368686180127)
        ·
          refine ⟨10812444067598053029270191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208296045065368686180127 10812444067598053029270191)
          ·
            refine ⟨16218666101397079543905287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10812444067598053029270191 16218666101397079543905287)
            ·
              refine ⟨24327999152095619315857931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218666101397079543905287 24327999152095619315857931)
              ·
                refine ⟨36491998728143428973786897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24327999152095619315857931 36491998728143428973786897)
                ·
                  refine ⟨27368999046107571730340173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36491998728143428973786897 27368999046107571730340173)
                  ·
                    refine ⟨10263374642290339398877565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27368999046107571730340173 10263374642290339398877565)
                    ·
                      refine ⟨3848765490858877274579087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263374642290339398877565 3848765490858877274579087)
                      ·
                        rfl

theorem cell23_7495444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7495444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495444 prefixEnd_7495444 := by exact prefixLift 7495444
  have htrace : WordTrace (prefixWord ++ tailWord_7495444) baseStart_7495444 baseEnd_7495444 := by
    simpa [prefixWord, tailWord_7495444, baseEnd_7495444] using wordTrace_append hprefix tailTrace_7495444
  have hstable : (prefixWord ++ tailWord_7495444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495444).length < 2 ^ (prefixWord ++ tailWord_7495444).sum := by decide
  have hdescent : baseEnd_7495444 < baseStart_7495444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495450 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_7495450 : Nat := 118140960795 + 7495450 * 2 ^ 59
def prefixEnd_7495450 : Nat := 4983230072969 + 3 ^ 40 * 7495450 * 2
def baseEnd_7495450 : Nat := 3848768571742804251104059

theorem tailTrace_7495450 : CollatzResearch.WordTrace tailWord_7495450 prefixEnd_7495450 3848768571742804251104059 := by
  unfold tailWord_7495450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68345380173818061447368951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182254347130181497192983869 68345380173818061447368951)
  ·
    refine ⟨102518070260727092171053427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68345380173818061447368951 102518070260727092171053427)
    ·
      refine ⟨153777105391090638256580141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102518070260727092171053427 153777105391090638256580141)
      ·
        refine ⟨57666414521658989346217553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153777105391090638256580141 57666414521658989346217553)
        ·
          refine ⟨43249810891244242009663165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57666414521658989346217553 43249810891244242009663165)
          ·
            refine ⟨16218679084216590753623687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43249810891244242009663165 16218679084216590753623687)
            ·
              refine ⟨24328018626324886130435531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218679084216590753623687 24328018626324886130435531)
              ·
                refine ⟨36492027939487329195653297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24328018626324886130435531 36492027939487329195653297)
                ·
                  refine ⟨27369020954615496896739973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36492027939487329195653297 27369020954615496896739973)
                  ·
                    refine ⟨5131691428990405668138745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27369020954615496896739973 5131691428990405668138745)
                    ·
                      refine ⟨3848768571742804251104059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131691428990405668138745 3848768571742804251104059)
                      ·
                        rfl

theorem cell23_7495450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_7495450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495450 prefixEnd_7495450 := by exact prefixLift 7495450
  have htrace : WordTrace (prefixWord ++ tailWord_7495450) baseStart_7495450 baseEnd_7495450 := by
    simpa [prefixWord, tailWord_7495450, baseEnd_7495450] using wordTrace_append hprefix tailTrace_7495450
  have hstable : (prefixWord ++ tailWord_7495450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495450).length < 2 ^ (prefixWord ++ tailWord_7495450).sum := by decide
  have hdescent : baseEnd_7495450 < baseStart_7495450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495460 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_7495460 : Nat := 118140960795 + 7495460 * 2 ^ 59
def prefixEnd_7495460 : Nat := 4983230072969 + 3 ^ 40 * 7495460 * 2
def baseEnd_7495460 : Nat := 1282924568849783070659671

theorem tailTrace_7495460 : CollatzResearch.WordTrace tailWord_7495460 prefixEnd_7495460 1282924568849783070659671 := by
  unfold tailWord_7495460
  simp only [CollatzResearch.WordTrace]
  refine ⟨136690942712618008748669917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182254590283490678331559889 136690942712618008748669917)
  ·
    refine ⟨51259103517231753280751219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136690942712618008748669917 51259103517231753280751219)
    ·
      refine ⟨76888655275847629921126829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51259103517231753280751219 76888655275847629921126829)
      ·
        refine ⟨28833245728442861220422561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76888655275847629921126829 28833245728442861220422561)
        ·
          refine ⟨21624934296332145915316921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28833245728442861220422561 21624934296332145915316921)
          ·
            refine ⟨16218700722249109436487691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21624934296332145915316921 16218700722249109436487691)
            ·
              refine ⟨24328051083373664154731537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218700722249109436487691 24328051083373664154731537)
              ·
                refine ⟨18246038312530248116048653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24328051083373664154731537 18246038312530248116048653)
                ·
                  refine ⟨6842264367198843043518245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18246038312530248116048653 6842264367198843043518245)
                  ·
                    refine ⟨1282924568849783070659671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842264367198843043518245 1282924568849783070659671)
                    ·
                      rfl

theorem cell23_7495460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_7495460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495460 prefixEnd_7495460 := by exact prefixLift 7495460
  have htrace : WordTrace (prefixWord ++ tailWord_7495460) baseStart_7495460 baseEnd_7495460 := by
    simpa [prefixWord, tailWord_7495460, baseEnd_7495460] using wordTrace_append hprefix tailTrace_7495460
  have hstable : (prefixWord ++ tailWord_7495460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495460).length < 2 ^ (prefixWord ++ tailWord_7495460).sum := by decide
  have hdescent : baseEnd_7495460 < baseStart_7495460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495494 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_7495494 : Nat := 118140960795 + 7495494 * 2 ^ 59
def prefixEnd_7495494 : Nat := 4983230072969 + 3 ^ 40 * 7495494 * 2
def baseEnd_7495494 : Nat := 1282930388297200692984619

theorem tailTrace_7495494 : CollatzResearch.WordTrace tailWord_7495494 prefixEnd_7495494 1282930388297200692984619 := by
  unfold tailWord_7495494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543222672097276290752423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182255417004741894202718357 8543222672097276290752423)
  ·
    refine ⟨12814834008145914436128635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543222672097276290752423 12814834008145914436128635)
    ·
      refine ⟨19222251012218871654192953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12814834008145914436128635 19222251012218871654192953)
      ·
        refine ⟨14416688259164153740644715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222251012218871654192953 14416688259164153740644715)
        ·
          refine ⟨21625032388746230610967073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416688259164153740644715 21625032388746230610967073)
          ·
            refine ⟨16218774291559672958225305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21625032388746230610967073 16218774291559672958225305)
            ·
              refine ⟨12164080718669754718668979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16218774291559672958225305 12164080718669754718668979)
              ·
                refine ⟨18246121078004632078003469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12164080718669754718668979 18246121078004632078003469)
                ·
                  refine ⟨6842295404251737029251301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18246121078004632078003469 6842295404251737029251301)
                  ·
                    refine ⟨1282930388297200692984619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842295404251737029251301 1282930388297200692984619)
                    ·
                      rfl

theorem cell23_7495494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_7495494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495494 prefixEnd_7495494 := by exact prefixLift 7495494
  have htrace : WordTrace (prefixWord ++ tailWord_7495494) baseStart_7495494 baseEnd_7495494 := by
    simpa [prefixWord, tailWord_7495494, baseEnd_7495494] using wordTrace_append hprefix tailTrace_7495494
  have hstable : (prefixWord ++ tailWord_7495494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495494).length < 2 ^ (prefixWord ++ tailWord_7495494).sum := by decide
  have hdescent : baseEnd_7495494 < baseStart_7495494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495520 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_7495520 : Nat := 118140960795 + 7495520 * 2 ^ 59
def prefixEnd_7495520 : Nat := 4983230072969 + 3 ^ 40 * 7495520 * 2
def baseEnd_7495520 : Nat := 1282934838462872992409579

theorem tailTrace_7495520 : CollatzResearch.WordTrace tailWord_7495520 prefixEnd_7495520 1282934838462872992409579 := by
  unfold tailWord_7495520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136692036902509323872262007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182256049203345765163016009 136692036902509323872262007)
  ·
    refine ⟨205038055353763985808393011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136692036902509323872262007 205038055353763985808393011)
    ·
      refine ⟨307557083030645978712589517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205038055353763985808393011 307557083030645978712589517)
      ·
        refine ⟨115333906136492242017221069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307557083030645978712589517 115333906136492242017221069)
        ·
          refine ⟨43250214801184590756457901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115333906136492242017221069 43250214801184590756457901)
          ·
            refine ⟨16218830550444221533671713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43250214801184590756457901 16218830550444221533671713)
            ·
              refine ⟨12164122912833166150253785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16218830550444221533671713 12164122912833166150253785)
              ·
                refine ⟨9123092184624874612690339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12164122912833166150253785 9123092184624874612690339)
                ·
                  refine ⟨13684638276937311919035509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123092184624874612690339 13684638276937311919035509)
                  ·
                    refine ⟨1282934838462872992409579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13684638276937311919035509 1282934838462872992409579)
                    ·
                      rfl

theorem cell23_7495520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_7495520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495520 prefixEnd_7495520 := by exact prefixLift 7495520
  have htrace : WordTrace (prefixWord ++ tailWord_7495520) baseStart_7495520 baseEnd_7495520 := by
    simpa [prefixWord, tailWord_7495520, baseEnd_7495520] using wordTrace_append hprefix tailTrace_7495520
  have hstable : (prefixWord ++ tailWord_7495520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495520).length < 2 ^ (prefixWord ++ tailWord_7495520).sum := by decide
  have hdescent : baseEnd_7495520 < baseStart_7495520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495533 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_7495533 : Nat := 118140960795 + 7495533 * 2 ^ 59
def prefixEnd_7495533 : Nat := 4983230072969 + 3 ^ 40 * 7495533 * 2
def baseEnd_7495533 : Nat := 1282937063545709142122059

theorem tailTrace_7495533 : CollatzResearch.WordTrace tailWord_7495533 prefixEnd_7495533 1282937063545709142122059 := by
  unfold tailWord_7495533
  simp only [CollatzResearch.WordTrace]
  refine ⟨273384547953971550964747253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182256365302647700643164835 273384547953971550964747253)
  ·
    refine ⟨25629801370684832902945055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273384547953971550964747253 25629801370684832902945055)
    ·
      refine ⟨38444702056027249354417583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25629801370684832902945055 38444702056027249354417583)
      ·
        refine ⟨57667053084040874031626375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38444702056027249354417583 57667053084040874031626375)
        ·
          refine ⟨86500579626061311047439563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57667053084040874031626375 86500579626061311047439563)
          ·
            refine ⟨129750869439091966571159345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86500579626061311047439563 129750869439091966571159345)
            ·
              refine ⟨97313152079318974928369509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129750869439091966571159345 97313152079318974928369509)
              ·
                refine ⟨18246216014872307799069283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97313152079318974928369509 18246216014872307799069283)
                ·
                  refine ⟨27369324022308461698603925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18246216014872307799069283 27369324022308461698603925)
                  ·
                    refine ⟨1282937063545709142122059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27369324022308461698603925 1282937063545709142122059)
                    ·
                      rfl

theorem cell23_7495533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_7495533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495533 prefixEnd_7495533 := by exact prefixLift 7495533
  have htrace : WordTrace (prefixWord ++ tailWord_7495533) baseStart_7495533 baseEnd_7495533 := by
    simpa [prefixWord, tailWord_7495533, baseEnd_7495533] using wordTrace_append hprefix tailTrace_7495533
  have hstable : (prefixWord ++ tailWord_7495533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495533).length < 2 ^ (prefixWord ++ tailWord_7495533).sum := by decide
  have hdescent : baseEnd_7495533 < baseStart_7495533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495543 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_7495543 : Nat := 118140960795 + 7495543 * 2 ^ 59
def prefixEnd_7495543 : Nat := 4983230072969 + 3 ^ 40 * 7495543 * 2
def baseEnd_7495543 : Nat := 3848816325443672387241131

theorem tailTrace_7495543 : CollatzResearch.WordTrace tailWord_7495543 prefixEnd_7495543 3848816325443672387241131 := by
  unfold tailWord_7495543
  simp only [CollatzResearch.WordTrace]
  refine ⟨273384912683935322672611283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182256608455956881781740855 273384912683935322672611283)
  ·
    refine ⟨410077369025902984008916925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273384912683935322672611283 410077369025902984008916925)
    ·
      refine ⟨153779013384713619003343847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410077369025902984008916925 153779013384713619003343847)
      ·
        refine ⟨230668520077070428505015771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153779013384713619003343847 230668520077070428505015771)
        ·
          refine ⟨346002780115605642757523657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230668520077070428505015771 346002780115605642757523657)
          ·
            refine ⟨259502085086704232068142743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346002780115605642757523657 259502085086704232068142743)
            ·
              refine ⟨389253127630056348102214115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259502085086704232068142743 389253127630056348102214115)
              ·
                refine ⟨583879691445084522153321173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389253127630056348102214115 583879691445084522153321173)
                ·
                  refine ⟨13684680268244168487968465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 583879691445084522153321173 13684680268244168487968465)
                  ·
                    refine ⟨10263510201183126365976349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13684680268244168487968465 10263510201183126365976349)
                    ·
                      refine ⟨3848816325443672387241131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263510201183126365976349 3848816325443672387241131)
                      ·
                        rfl

theorem cell23_7495543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_7495543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495543 prefixEnd_7495543 := by exact prefixLift 7495543
  have htrace : WordTrace (prefixWord ++ tailWord_7495543) baseStart_7495543 baseEnd_7495543 := by
    simpa [prefixWord, tailWord_7495543, baseEnd_7495543] using wordTrace_append hprefix tailTrace_7495543
  have hstable : (prefixWord ++ tailWord_7495543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495543).length < 2 ^ (prefixWord ++ tailWord_7495543).sum := by decide
  have hdescent : baseEnd_7495543 < baseStart_7495543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495546 : List Nat := [3, 1, 1, 1, 1, 1, 15]
def baseStart_7495546 : Nat := 118140960795 + 7495546 * 2 ^ 59
def prefixEnd_7495546 : Nat := 4983230072969 + 3 ^ 40 * 7495546 * 2
def baseEnd_7495546 : Nat := 47516269949205381179057

theorem tailTrace_7495546 : CollatzResearch.WordTrace tailWord_7495546 prefixEnd_7495546 47516269949205381179057 := by
  unfold tailWord_7495546
  simp only [CollatzResearch.WordTrace]
  refine ⟨68346255525731113546242623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182256681401949636123313661 68346255525731113546242623)
  ·
    refine ⟨102519383288596670319363935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68346255525731113546242623 102519383288596670319363935)
    ·
      refine ⟨153779074932895005479045903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102519383288596670319363935 153779074932895005479045903)
      ·
        refine ⟨230668612399342508218568855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153779074932895005479045903 230668612399342508218568855)
        ·
          refine ⟨346002918599013762327853283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230668612399342508218568855 346002918599013762327853283)
          ·
            refine ⟨519004377898520643491779925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346002918599013762327853283 519004377898520643491779925)
            ·
              refine ⟨47516269949205381179057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 519004377898520643491779925 47516269949205381179057)
              ·
                rfl

theorem cell23_7495546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 15].length) (baseStart_7495546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495546 prefixEnd_7495546 := by exact prefixLift 7495546
  have htrace : WordTrace (prefixWord ++ tailWord_7495546) baseStart_7495546 baseEnd_7495546 := by
    simpa [prefixWord, tailWord_7495546, baseEnd_7495546] using wordTrace_append hprefix tailTrace_7495546
  have hstable : (prefixWord ++ tailWord_7495546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495546).length < 2 ^ (prefixWord ++ tailWord_7495546).sum := by decide
  have hdescent : baseEnd_7495546 < baseStart_7495546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495570 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7495570 : Nat := 118140960795 + 7495570 * 2 ^ 59
def prefixEnd_7495570 : Nat := 4983230072969 + 3 ^ 40 * 7495570 * 2
def baseEnd_7495570 : Nat := 3848830189421343781603507

theorem tailTrace_7495570 : CollatzResearch.WordTrace tailWord_7495570 prefixEnd_7495570 3848830189421343781603507 := by
  unfold tailWord_7495570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68346474363709376570961041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182257264969891670855896109 68346474363709376570961041)
  ·
    refine ⟨51259855772782032428220781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68346474363709376570961041 51259855772782032428220781)
    ·
      refine ⟨19222445914793262160582793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51259855772782032428220781 19222445914793262160582793)
      ·
        refine ⟨14416834436094946620437095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222445914793262160582793 14416834436094946620437095)
        ·
          refine ⟨21625251654142419930655643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416834436094946620437095 21625251654142419930655643)
          ·
            refine ⟨32437877481213629895983465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21625251654142419930655643 32437877481213629895983465)
            ·
              refine ⟨24328408110910222421987599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32437877481213629895983465 24328408110910222421987599)
              ·
                refine ⟨36492612166365333632981399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24328408110910222421987599 36492612166365333632981399)
                ·
                  refine ⟨54738918249548000449472099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36492612166365333632981399 54738918249548000449472099)
                  ·
                    refine ⟨82108377374322000674208149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54738918249548000449472099 82108377374322000674208149)
                    ·
                      refine ⟨3848830189421343781603507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82108377374322000674208149 3848830189421343781603507)
                      ·
                        rfl

theorem cell23_7495570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7495570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495570 prefixEnd_7495570 := by exact prefixLift 7495570
  have htrace : WordTrace (prefixWord ++ tailWord_7495570) baseStart_7495570 baseEnd_7495570 := by
    simpa [prefixWord, tailWord_7495570, baseEnd_7495570] using wordTrace_append hprefix tailTrace_7495570
  have hstable : (prefixWord ++ tailWord_7495570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495570).length < 2 ^ (prefixWord ++ tailWord_7495570).sum := by decide
  have hdescent : baseEnd_7495570 < baseStart_7495570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495633 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7495633 : Nat := 118140960795 + 7495633 * 2 ^ 59
def prefixEnd_7495633 : Nat := 4983230072969 + 3 ^ 40 * 7495633 * 2
def baseEnd_7495633 : Nat := 3848862538702577035115717

theorem tailTrace_7495633 : CollatzResearch.WordTrace tailWord_7495633 prefixEnd_7495633 3848862538702577035115717 := by
  unfold tailWord_7495633
  simp only [CollatzResearch.WordTrace]
  refine ⟨273388195253609268043387553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182258796835739512028925035 273388195253609268043387553)
  ·
    refine ⟨205041146440206951032540665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273388195253609268043387553 205041146440206951032540665)
    ·
      refine ⟨153780859830155213274405499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205041146440206951032540665 153780859830155213274405499)
      ·
        refine ⟨230671289745232819911608249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153780859830155213274405499 230671289745232819911608249)
        ·
          refine ⟨173003467308924614933706187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230671289745232819911608249 173003467308924614933706187)
          ·
            refine ⟨259505200963386922400559281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173003467308924614933706187 259505200963386922400559281)
            ·
              refine ⟨194628900722540191800419461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259505200963386922400559281 194628900722540191800419461)
              ·
                refine ⟨36492918885476285962578649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194628900722540191800419461 36492918885476285962578649)
                ·
                  refine ⟨27369689164107214471933987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36492918885476285962578649 27369689164107214471933987)
                  ·
                    refine ⟨41054533746160821707900981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27369689164107214471933987 41054533746160821707900981)
                    ·
                      refine ⟨3848862538702577035115717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41054533746160821707900981 3848862538702577035115717)
                      ·
                        rfl

theorem cell23_7495633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7495633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495633 prefixEnd_7495633 := by exact prefixLift 7495633
  have htrace : WordTrace (prefixWord ++ tailWord_7495633) baseStart_7495633 baseEnd_7495633 := by
    simpa [prefixWord, tailWord_7495633, baseEnd_7495633] using wordTrace_append hprefix tailTrace_7495633
  have hstable : (prefixWord ++ tailWord_7495633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495633).length < 2 ^ (prefixWord ++ tailWord_7495633).sum := by decide
  have hdescent : baseEnd_7495633 < baseStart_7495633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495647 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 4, 2]
def baseStart_7495647 : Nat := 118140960795 + 7495647 * 2 ^ 59
def prefixEnd_7495647 : Nat := 4983230072969 + 3 ^ 40 * 7495647 * 2
def baseEnd_7495647 : Nat := 3848869727431739980340653

theorem tailTrace_7495647 : CollatzResearch.WordTrace tailWord_7495647 prefixEnd_7495647 3848869727431739980340653 := by
  unfold tailWord_7495647
  simp only [CollatzResearch.WordTrace]
  refine ⟨273388705875558548434397195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182259137250372365622931463 273388705875558548434397195)
  ·
    refine ⟨410083058813337822651595793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273388705875558548434397195 410083058813337822651595793)
    ·
      refine ⟨307562294110003366988696845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410083058813337822651595793 307562294110003366988696845)
      ·
        refine ⟨115335860291251262620761317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307562294110003366988696845 115335860291251262620761317)
        ·
          refine ⟨21625473804609611741392747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115335860291251262620761317 21625473804609611741392747)
          ·
            refine ⟨32438210706914417612089121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21625473804609611741392747 32438210706914417612089121)
            ·
              refine ⟨24328658030185813209066841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32438210706914417612089121 24328658030185813209066841)
              ·
                refine ⟨18246493522639359906800131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24328658030185813209066841 18246493522639359906800131)
                ·
                  refine ⟨27369740283959039860200197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18246493522639359906800131 27369740283959039860200197)
                  ·
                    refine ⟨5131826303242319973787537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27369740283959039860200197 5131826303242319973787537)
                    ·
                      refine ⟨3848869727431739980340653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131826303242319973787537 3848869727431739980340653)
                      ·
                        rfl

theorem cell23_7495647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_7495647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495647 prefixEnd_7495647 := by exact prefixLift 7495647
  have htrace : WordTrace (prefixWord ++ tailWord_7495647) baseStart_7495647 baseEnd_7495647 := by
    simpa [prefixWord, tailWord_7495647, baseEnd_7495647] using wordTrace_append hprefix tailTrace_7495647
  have hstable : (prefixWord ++ tailWord_7495647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495647).length < 2 ^ (prefixWord ++ tailWord_7495647).sum := by decide
  have hdescent : baseEnd_7495647 < baseStart_7495647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495651 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7495651 : Nat := 118140960795 + 7495651 * 2 ^ 59
def prefixEnd_7495651 : Nat := 4983230072969 + 3 ^ 40 * 7495651 * 2
def baseEnd_7495651 : Nat := 3848871781354357964690635

theorem tailTrace_7495651 : CollatzResearch.WordTrace tailWord_7495651 prefixEnd_7495651 3848871781354357964690635 := by
  unfold tailWord_7495651
  simp only [CollatzResearch.WordTrace]
  refine ⟨273388851767544057117542807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182259234511696038078361871 273388851767544057117542807)
  ·
    refine ⟨410083277651316085676314211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273388851767544057117542807 410083277651316085676314211)
    ·
      refine ⟨615124916476974128514471317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410083277651316085676314211 615124916476974128514471317)
      ·
        refine ⟨28833980459858162274115843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 615124916476974128514471317 28833980459858162274115843)
        ·
          refine ⟨43250970689787243411173765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28833980459858162274115843 43250970689787243411173765)
          ·
            refine ⟨8109557004335108139595081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43250970689787243411173765 8109557004335108139595081)
            ·
              refine ⟨6082167753251331104696311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109557004335108139595081 6082167753251331104696311)
              ·
                refine ⟨9123251629876996657044467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082167753251331104696311 9123251629876996657044467)
                ·
                  refine ⟨13684877444815494985566701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123251629876996657044467 13684877444815494985566701)
                  ·
                    refine ⟨5131829041805810619587513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13684877444815494985566701 5131829041805810619587513)
                    ·
                      refine ⟨3848871781354357964690635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131829041805810619587513 3848871781354357964690635)
                      ·
                        rfl

theorem cell23_7495651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7495651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495651 prefixEnd_7495651 := by exact prefixLift 7495651
  have htrace : WordTrace (prefixWord ++ tailWord_7495651) baseStart_7495651 baseEnd_7495651 := by
    simpa [prefixWord, tailWord_7495651, baseEnd_7495651] using wordTrace_append hprefix tailTrace_7495651
  have hstable : (prefixWord ++ tailWord_7495651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495651).length < 2 ^ (prefixWord ++ tailWord_7495651).sum := by decide
  have hdescent : baseEnd_7495651 < baseStart_7495651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495664 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2]
def baseStart_7495664 : Nat := 118140960795 + 7495664 * 2 ^ 59
def prefixEnd_7495664 : Nat := 4983230072969 + 3 ^ 40 * 7495664 * 2
def baseEnd_7495664 : Nat := 3848878456602866413828075

theorem tailTrace_7495664 : CollatzResearch.WordTrace tailWord_7495664 prefixEnd_7495664 3848878456602866413828075 := by
  unfold tailWord_7495664
  simp only [CollatzResearch.WordTrace]
  refine ⟨136694662958248480168883023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182259550610997973558510697 136694662958248480168883023)
  ·
    refine ⟨205041994437372720253324535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136694662958248480168883023 205041994437372720253324535)
    ·
      refine ⟨307562991656059080379986803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205041994437372720253324535 307562991656059080379986803)
      ·
        refine ⟨461344487484088620569980205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307562991656059080379986803 461344487484088620569980205)
        ·
          refine ⟨173004182806533232713742577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461344487484088620569980205 173004182806533232713742577)
          ·
            refine ⟨129753137104899924535306933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173004182806533232713742577 129753137104899924535306933)
            ·
              refine ⟨12164356603584367925185025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129753137104899924535306933 12164356603584367925185025)
              ·
                refine ⟨9123267452688275943888769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12164356603584367925185025 9123267452688275943888769)
                ·
                  refine ⟨6842450589516206957916577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123267452688275943888769 6842450589516206957916577)
                  ·
                    refine ⟨5131837942137155218437433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842450589516206957916577 5131837942137155218437433)
                    ·
                      refine ⟨3848878456602866413828075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131837942137155218437433 3848878456602866413828075)
                      ·
                        rfl

theorem cell23_7495664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2].length) (baseStart_7495664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495664 prefixEnd_7495664 := by exact prefixLift 7495664
  have htrace : WordTrace (prefixWord ++ tailWord_7495664) baseStart_7495664 baseEnd_7495664 := by
    simpa [prefixWord, tailWord_7495664, baseEnd_7495664] using wordTrace_append hprefix tailTrace_7495664
  have hstable : (prefixWord ++ tailWord_7495664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495664).length < 2 ^ (prefixWord ++ tailWord_7495664).sum := by decide
  have hdescent : baseEnd_7495664 < baseStart_7495664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495681 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_7495681 : Nat := 118140960795 + 7495681 * 2 ^ 59
def prefixEnd_7495681 : Nat := 4983230072969 + 3 ^ 40 * 7495681 * 2
def baseEnd_7495681 : Nat := 3848887185773992847315497

theorem tailTrace_7495681 : CollatzResearch.WordTrace tailWord_7495681 prefixEnd_7495681 3848887185773992847315497 := by
  unfold tailWord_7495681
  simp only [CollatzResearch.WordTrace]
  refine ⟨273389945957435372241134897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182259963971623581494089931 273389945957435372241134897)
  ·
    refine ⟨205042459468076529180851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273389945957435372241134897 205042459468076529180851173)
    ·
      refine ⟨38445461150264349221409595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205042459468076529180851173 38445461150264349221409595)
      ·
        refine ⟨57668191725396523832114393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38445461150264349221409595 57668191725396523832114393)
        ·
          refine ⟨43251143794047392874085795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57668191725396523832114393 43251143794047392874085795)
          ·
            refine ⟨64876715691071089311128693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43251143794047392874085795 64876715691071089311128693)
            ·
              refine ⟨6082192096037914622918315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64876715691071089311128693 6082192096037914622918315)
              ·
                refine ⟨9123288144056871934377473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082192096037914622918315 9123288144056871934377473)
                ·
                  refine ⟨6842466108042653950783105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123288144056871934377473 6842466108042653950783105)
                  ·
                    refine ⟨5131849581031990463087329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842466108042653950783105 5131849581031990463087329)
                    ·
                      refine ⟨3848887185773992847315497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131849581031990463087329 3848887185773992847315497)
                      ·
                        rfl

theorem cell23_7495681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_7495681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495681 prefixEnd_7495681 := by exact prefixLift 7495681
  have htrace : WordTrace (prefixWord ++ tailWord_7495681) baseStart_7495681 baseEnd_7495681 := by
    simpa [prefixWord, tailWord_7495681, baseEnd_7495681] using wordTrace_append hprefix tailTrace_7495681
  have hstable : (prefixWord ++ tailWord_7495681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495681).length < 2 ^ (prefixWord ++ tailWord_7495681).sum := by decide
  have hdescent : baseEnd_7495681 < baseStart_7495681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495723 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_7495723 : Nat := 118140960795 + 7495723 * 2 ^ 59
def prefixEnd_7495723 : Nat := 4983230072969 + 3 ^ 40 * 7495723 * 2
def baseEnd_7495723 : Nat := 3848908751961481682990303

theorem tailTrace_7495723 : CollatzResearch.WordTrace tailWord_7495723 prefixEnd_7495723 3848908751961481682990303 := by
  unfold tailWord_7495723
  simp only [CollatzResearch.WordTrace]
  refine ⟨273391477823283213414163823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182260985215522142276109215 273391477823283213414163823)
  ·
    refine ⟨410087216734924820121245735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273391477823283213414163823 410087216734924820121245735)
    ·
      refine ⟨615130825102387230181868603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410087216734924820121245735 615130825102387230181868603)
      ·
        refine ⟨922696237653580845272802905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615130825102387230181868603 922696237653580845272802905)
        ·
          refine ⟨692022178240185633954602179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922696237653580845272802905 692022178240185633954602179)
          ·
            refine ⟨1038033267360278450931903269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692022178240185633954602179 1038033267360278450931903269)
            ·
              refine ⟨194631237630052209549731863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1038033267360278450931903269 194631237630052209549731863)
              ·
                refine ⟨291946856445078314324597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194631237630052209549731863 291946856445078314324597795)
                ·
                  refine ⟨437920284667617471486896693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291946856445078314324597795 437920284667617471486896693)
                  ·
                    refine ⟨41055026687589137951896565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437920284667617471486896693 41055026687589137951896565)
                    ·
                      refine ⟨3848908751961481682990303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41055026687589137951896565 3848908751961481682990303)
                      ·
                        rfl

theorem cell23_7495723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_7495723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495723 prefixEnd_7495723 := by exact prefixLift 7495723
  have htrace : WordTrace (prefixWord ++ tailWord_7495723) baseStart_7495723 baseEnd_7495723 := by
    simpa [prefixWord, tailWord_7495723, baseEnd_7495723] using wordTrace_append hprefix tailTrace_7495723
  have hstable : (prefixWord ++ tailWord_7495723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495723).length < 2 ^ (prefixWord ++ tailWord_7495723).sum := by decide
  have hdescent : baseEnd_7495723 < baseStart_7495723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495732 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_7495732 : Nat := 118140960795 + 7495732 * 2 ^ 59
def prefixEnd_7495732 : Nat := 4983230072969 + 3 ^ 40 * 7495732 * 2
def baseEnd_7495732 : Nat := 3848913373287372147777763

theorem tailTrace_7495732 : CollatzResearch.WordTrace tailWord_7495732 prefixEnd_7495732 3848913373287372147777763 := by
  unfold tailWord_7495732
  simp only [CollatzResearch.WordTrace]
  refine ⟨136695903040125303975620725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182261204053500405300827633 136695903040125303975620725)
  ·
    refine ⟨12815240910011747247714443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136695903040125303975620725 12815240910011747247714443)
    ·
      refine ⟨19222861365017620871571665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815240910011747247714443 19222861365017620871571665)
      ·
        refine ⟨14417146023763215653678749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222861365017620871571665 14417146023763215653678749)
        ·
          refine ⟨5406429758911205870129531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14417146023763215653678749 5406429758911205870129531)
          ·
            refine ⟨8109644638366808805194297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406429758911205870129531 8109644638366808805194297)
            ·
              refine ⟨6082233478775106603895723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109644638366808805194297 6082233478775106603895723)
              ·
                refine ⟨9123350218162659905843585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082233478775106603895723 9123350218162659905843585)
                ·
                  refine ⟨6842512663621994929382689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123350218162659905843585 6842512663621994929382689)
                  ·
                    refine ⟨5131884497716496197037017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842512663621994929382689 5131884497716496197037017)
                    ·
                      refine ⟨3848913373287372147777763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5131884497716496197037017 3848913373287372147777763)
                      ·
                        rfl

theorem cell23_7495732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_7495732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495732 prefixEnd_7495732 := by exact prefixLift 7495732
  have htrace : WordTrace (prefixWord ++ tailWord_7495732) baseStart_7495732 baseEnd_7495732 := by
    simpa [prefixWord, tailWord_7495732, baseEnd_7495732] using wordTrace_append hprefix tailTrace_7495732
  have hstable : (prefixWord ++ tailWord_7495732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495732).length < 2 ^ (prefixWord ++ tailWord_7495732).sum := by decide
  have hdescent : baseEnd_7495732 < baseStart_7495732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495764 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_7495764 : Nat := 118140960795 + 7495764 * 2 ^ 59
def prefixEnd_7495764 : Nat := 4983230072969 + 3 ^ 40 * 7495764 * 2
def baseEnd_7495764 : Nat := 1282976601556105340859205

theorem tailTrace_7495764 : CollatzResearch.WordTrace tailWord_7495764 prefixEnd_7495764 1282976601556105340859205 := by
  unfold tailWord_7495764
  simp only [CollatzResearch.WordTrace]
  refine ⟨136696486608067338708203173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182261982144089784944270897 136696486608067338708203173)
  ·
    refine ⟨25630591239012626007788095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136696486608067338708203173 25630591239012626007788095)
    ·
      refine ⟨38445886858518939011682143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25630591239012626007788095 38445886858518939011682143)
      ·
        refine ⟨57668830287778408517523215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38445886858518939011682143 57668830287778408517523215)
        ·
          refine ⟨86503245431667612776284823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57668830287778408517523215 86503245431667612776284823)
          ·
            refine ⟨129754868147501419164427235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86503245431667612776284823 129754868147501419164427235)
            ·
              refine ⟨194632302221252128746640853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129754868147501419164427235 194632302221252128746640853)
              ·
                refine ⟨4561694583310596767499395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194632302221252128746640853 4561694583310596767499395)
                ·
                  refine ⟨6842541874965895151249093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561694583310596767499395 6842541874965895151249093)
                  ·
                    refine ⟨1282976601556105340859205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842541874965895151249093 1282976601556105340859205)
                    ·
                      rfl

theorem cell23_7495764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_7495764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495764 prefixEnd_7495764 := by exact prefixLift 7495764
  have htrace : WordTrace (prefixWord ++ tailWord_7495764) baseStart_7495764 baseEnd_7495764 := by
    simpa [prefixWord, tailWord_7495764, baseEnd_7495764] using wordTrace_append hprefix tailTrace_7495764
  have hstable : (prefixWord ++ tailWord_7495764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495764).length < 2 ^ (prefixWord ++ tailWord_7495764).sum := by decide
  have hdescent : baseEnd_7495764 < baseStart_7495764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495781 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_7495781 : Nat := 118140960795 + 7495781 * 2 ^ 59
def prefixEnd_7495781 : Nat := 4983230072969 + 3 ^ 40 * 7495781 * 2
def baseEnd_7495781 : Nat := 1282979511279814152021679

theorem tailTrace_7495781 : CollatzResearch.WordTrace tailWord_7495781 prefixEnd_7495781 1282979511279814152021679 := by
  unfold tailWord_7495781
  simp only [CollatzResearch.WordTrace]
  refine ⟨273393593257073089319775197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182262395504715392879850131 273393593257073089319775197)
  ·
    refine ⟨102522597471402408494915699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273393593257073089319775197 102522597471402408494915699)
    ·
      refine ⟨153783896207103612742373549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102522597471402408494915699 153783896207103612742373549)
      ·
        refine ⟨57668961077663854778390081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153783896207103612742373549 57668961077663854778390081)
        ·
          refine ⟨43251720808247891083792561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57668961077663854778390081 43251720808247891083792561)
          ·
            refine ⟨32438790606185918312844421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43251720808247891083792561 32438790606185918312844421)
            ·
              refine ⟨6082273238659859683658329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32438790606185918312844421 6082273238659859683658329)
              ·
                refine ⟨4561704928994894762743747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6082273238659859683658329 4561704928994894762743747)
                ·
                  refine ⟨6842557393492342144115621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561704928994894762743747 6842557393492342144115621)
                  ·
                    refine ⟨1282979511279814152021679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6842557393492342144115621 1282979511279814152021679)
                    ·
                      rfl

theorem cell23_7495781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_7495781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495781 prefixEnd_7495781 := by exact prefixLift 7495781
  have htrace : WordTrace (prefixWord ++ tailWord_7495781) baseStart_7495781 baseEnd_7495781 := by
    simpa [prefixWord, tailWord_7495781, baseEnd_7495781] using wordTrace_append hprefix tailTrace_7495781
  have hstable : (prefixWord ++ tailWord_7495781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495781).length < 2 ^ (prefixWord ++ tailWord_7495781).sum := by decide
  have hdescent : baseEnd_7495781 < baseStart_7495781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495804 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_7495804 : Nat := 118140960795 + 7495804 * 2 ^ 59
def prefixEnd_7495804 : Nat := 4983230072969 + 3 ^ 40 * 7495804 * 2
def baseEnd_7495804 : Nat := 3848950343894495866077431

theorem tailTrace_7495804 : CollatzResearch.WordTrace tailWord_7495804 prefixEnd_7495804 3848950343894495866077431 := by
  unfold tailWord_7495804
  simp only [CollatzResearch.WordTrace]
  refine ⟨136697216067994882123931233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182262954757326509498574977 136697216067994882123931233)
  ·
    refine ⟨102522912050996161592948425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136697216067994882123931233 102522912050996161592948425)
    ·
      refine ⟨76892184038247121194711319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102522912050996161592948425 76892184038247121194711319)
      ·
        refine ⟨115338276057370681792066979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76892184038247121194711319 115338276057370681792066979)
        ·
          refine ⟨173007414086056022688100469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115338276057370681792066979 173007414086056022688100469)
          ·
            refine ⟨16219445070567752127009419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173007414086056022688100469 16219445070567752127009419)
            ·
              refine ⟨24329167605851628190514129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219445070567752127009419 24329167605851628190514129)
              ·
                refine ⟨18246875704388721142885597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24329167605851628190514129 18246875704388721142885597)
                ·
                  refine ⟨6842578389145770428582099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18246875704388721142885597 6842578389145770428582099)
                  ·
                    refine ⟨10263867583718655642873149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6842578389145770428582099 10263867583718655642873149)
                    ·
                      refine ⟨3848950343894495866077431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263867583718655642873149 3848950343894495866077431)
                      ·
                        rfl

theorem cell23_7495804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_7495804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495804 prefixEnd_7495804 := by exact prefixLift 7495804
  have htrace : WordTrace (prefixWord ++ tailWord_7495804) baseStart_7495804 baseEnd_7495804 := by
    simpa [prefixWord, tailWord_7495804, baseEnd_7495804] using wordTrace_append hprefix tailTrace_7495804
  have hstable : (prefixWord ++ tailWord_7495804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495804).length < 2 ^ (prefixWord ++ tailWord_7495804).sum := by decide
  have hdescent : baseEnd_7495804 < baseStart_7495804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495828 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 6]
def baseStart_7495828 : Nat := 118140960795 + 7495828 * 2 ^ 59
def prefixEnd_7495828 : Nat := 4983230072969 + 3 ^ 40 * 7495828 * 2
def baseEnd_7495828 : Nat := 427662518603355974686369

theorem tailTrace_7495828 : CollatzResearch.WordTrace tailWord_7495828 prefixEnd_7495828 427662518603355974686369 := by
  unfold tailWord_7495828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136697653743951408173368069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182263538325268544231157425 136697653743951408173368069)
  ·
    refine ⟨25630810076990889032506513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136697653743951408173368069 25630810076990889032506513)
    ·
      refine ⟨19223107557743166774379885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25630810076990889032506513 19223107557743166774379885)
      ·
        refine ⟨7208665334153687540392457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19223107557743166774379885 7208665334153687540392457)
        ·
          refine ⟨5406499000615265655294343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7208665334153687540392457 5406499000615265655294343)
          ·
            refine ⟨8109748500922898482941515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406499000615265655294343 8109748500922898482941515)
            ·
              refine ⟨12164622751384347724412273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109748500922898482941515 12164622751384347724412273)
              ·
                refine ⟨9123467063538260793309205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12164622751384347724412273 9123467063538260793309205)
                ·
                  refine ⟨427662518603355974686369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9123467063538260793309205 427662518603355974686369)
                  ·
                    rfl

theorem cell23_7495828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_7495828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495828 prefixEnd_7495828 := by exact prefixLift 7495828
  have htrace : WordTrace (prefixWord ++ tailWord_7495828) baseStart_7495828 baseEnd_7495828 := by
    simpa [prefixWord, tailWord_7495828, baseEnd_7495828] using wordTrace_append hprefix tailTrace_7495828
  have hstable : (prefixWord ++ tailWord_7495828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495828).length < 2 ^ (prefixWord ++ tailWord_7495828).sum := by decide
  have hdescent : baseEnd_7495828 < baseStart_7495828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495838 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7495838 : Nat := 118140960795 + 7495838 * 2 ^ 59
def prefixEnd_7495838 : Nat := 4983230072969 + 3 ^ 40 * 7495838 * 2
def baseEnd_7495838 : Nat := 3848967802236748733052275

theorem tailTrace_7495838 : CollatzResearch.WordTrace tailWord_7495838 prefixEnd_7495838 3848967802236748733052275 := by
  unfold tailWord_7495838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174459027233323506825021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182263781478577725369733445 34174459027233323506825021)
  ·
    refine ⟨12815422135212496315059383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34174459027233323506825021 12815422135212496315059383)
    ·
      refine ⟨19223133202818744472589075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815422135212496315059383 19223133202818744472589075)
      ·
        refine ⟨28834699804228116708883613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223133202818744472589075 28834699804228116708883613)
        ·
          refine ⟨10813012426585543765831355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28834699804228116708883613 10813012426585543765831355)
          ·
            refine ⟨16219518639878315648747033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10813012426585543765831355 16219518639878315648747033)
            ·
              refine ⟨12164638979908736736560275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16219518639878315648747033 12164638979908736736560275)
              ·
                refine ⟨18246958469863105104840413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12164638979908736736560275 18246958469863105104840413)
                ·
                  refine ⟨6842609426198664414315155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18246958469863105104840413 6842609426198664414315155)
                  ·
                    refine ⟨10263914139297996621472733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6842609426198664414315155 10263914139297996621472733)
                    ·
                      refine ⟨3848967802236748733052275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263914139297996621472733 3848967802236748733052275)
                      ·
                        rfl

theorem cell23_7495838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7495838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495838 prefixEnd_7495838 := by exact prefixLift 7495838
  have htrace : WordTrace (prefixWord ++ tailWord_7495838) baseStart_7495838 baseEnd_7495838 := by
    simpa [prefixWord, tailWord_7495838, baseEnd_7495838] using wordTrace_append hprefix tailTrace_7495838
  have hstable : (prefixWord ++ tailWord_7495838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495838).length < 2 ^ (prefixWord ++ tailWord_7495838).sum := by decide
  have hdescent : baseEnd_7495838 < baseStart_7495838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495864 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_7495864 : Nat := 118140960795 + 7495864 * 2 ^ 59
def prefixEnd_7495864 : Nat := 4983230072969 + 3 ^ 40 * 7495864 * 2
def baseEnd_7495864 : Nat := 3848981152733765631327155

theorem tailTrace_7495864 : CollatzResearch.WordTrace tailWord_7495864 prefixEnd_7495864 3848981152733765631327155 := by
  unfold tailWord_7495864
  simp only [CollatzResearch.WordTrace]
  refine ⟨136698310257886197247523323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182264413677181596330031097 136698310257886197247523323)
  ·
    refine ⟨205047465386829295871284985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136698310257886197247523323 205047465386829295871284985)
    ·
      refine ⟨153785599040121971903463739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205047465386829295871284985 153785599040121971903463739)
      ·
        refine ⟨230678398560182957855195609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153785599040121971903463739 230678398560182957855195609)
        ·
          refine ⟨173008798920137218391396707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230678398560182957855195609 173008798920137218391396707)
          ·
            refine ⟨259513198380205827587095061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173008798920137218391396707 259513198380205827587095061)
            ·
              refine ⟨12164681174072148168145081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 259513198380205827587095061 12164681174072148168145081)
              ·
                refine ⟨9123510880554111126108811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12164681174072148168145081 9123510880554111126108811)
                ·
                  refine ⟨13685266320831166689163217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123510880554111126108811 13685266320831166689163217)
                  ·
                    refine ⟨10263949740623375016872413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13685266320831166689163217 10263949740623375016872413)
                    ·
                      refine ⟨3848981152733765631327155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263949740623375016872413 3848981152733765631327155)
                      ·
                        rfl

theorem cell23_7495864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_7495864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495864 prefixEnd_7495864 := by exact prefixLift 7495864
  have htrace : WordTrace (prefixWord ++ tailWord_7495864) baseStart_7495864 baseEnd_7495864 := by
    simpa [prefixWord, tailWord_7495864, baseEnd_7495864] using wordTrace_append hprefix tailTrace_7495864
  have hstable : (prefixWord ++ tailWord_7495864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495864).length < 2 ^ (prefixWord ++ tailWord_7495864).sum := by decide
  have hdescent : baseEnd_7495864 < baseStart_7495864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495877 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_7495877 : Nat := 118140960795 + 7495877 * 2 ^ 59
def prefixEnd_7495877 : Nat := 4983230072969 + 3 ^ 40 * 7495877 * 2
def baseEnd_7495877 : Nat := 3848987827982274080464595

theorem tailTrace_7495877 : CollatzResearch.WordTrace tailWord_7495877 prefixEnd_7495877 3848987827982274080464595 := by
  unfold tailWord_7495877
  simp only [CollatzResearch.WordTrace]
  refine ⟨273397094664725297715269885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182264729776483531810179923 273397094664725297715269885)
  ·
    refine ⟨102523910499271986643226207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273397094664725297715269885 102523910499271986643226207)
    ·
      refine ⟨153785865748907979964839311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102523910499271986643226207 153785865748907979964839311)
      ·
        refine ⟨230678798623361969947258967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153785865748907979964839311 230678798623361969947258967)
        ·
          refine ⟨346018197935042954920888451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230678798623361969947258967 346018197935042954920888451)
          ·
            refine ⟨519027296902564432381332677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346018197935042954920888451 519027296902564432381332677)
            ·
              refine ⟨97317618169230831071499877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519027296902564432381332677 97317618169230831071499877)
              ·
                refine ⟨18247053406730780825906227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97317618169230831071499877 18247053406730780825906227)
                ·
                  refine ⟨27370580110096171238859341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18247053406730780825906227 27370580110096171238859341)
                  ·
                    refine ⟨10263967541286064214572253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27370580110096171238859341 10263967541286064214572253)
                    ·
                      refine ⟨3848987827982274080464595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10263967541286064214572253 3848987827982274080464595)
                      ·
                        rfl

theorem cell23_7495877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_7495877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495877 prefixEnd_7495877 := by exact prefixLift 7495877
  have htrace : WordTrace (prefixWord ++ tailWord_7495877) baseStart_7495877 baseEnd_7495877 := by
    simpa [prefixWord, tailWord_7495877, baseEnd_7495877] using wordTrace_append hprefix tailTrace_7495877
  have hstable : (prefixWord ++ tailWord_7495877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495877).length < 2 ^ (prefixWord ++ tailWord_7495877).sum := by decide
  have hdescent : baseEnd_7495877 < baseStart_7495877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495880 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_7495880 : Nat := 118140960795 + 7495880 * 2 ^ 59
def prefixEnd_7495880 : Nat := 4983230072969 + 3 ^ 40 * 7495880 * 2
def baseEnd_7495880 : Nat := 1282996456141412522909027

theorem tailTrace_7495880 : CollatzResearch.WordTrace tailWord_7495880 prefixEnd_7495880 1282996456141412522909027 := by
  unfold tailWord_7495880
  simp only [CollatzResearch.WordTrace]
  refine ⟨136698602041857214613814547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182264802722476286151752729 136698602041857214613814547)
  ·
    refine ⟨205047903062785821920721821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136698602041857214613814547 205047903062785821920721821)
    ·
      refine ⟨76892963648544683220270683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205047903062785821920721821 76892963648544683220270683)
      ·
        refine ⟨115339445472817024830406025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76892963648544683220270683 115339445472817024830406025)
        ·
          refine ⟨86504584104612768622804519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115339445472817024830406025 86504584104612768622804519)
          ·
            refine ⟨129756876156919152934206779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86504584104612768622804519 129756876156919152934206779)
            ·
              refine ⟨194635314235378729401310169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129756876156919152934206779 194635314235378729401310169)
              ·
                refine ⟨145976485676534047050982627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194635314235378729401310169 145976485676534047050982627)
                ·
                  refine ⟨218964728514801070576473941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145976485676534047050982627 218964728514801070576473941)
                  ·
                    refine ⟨1282996456141412522909027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218964728514801070576473941 1282996456141412522909027)
                    ·
                      rfl

theorem cell23_7495880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_7495880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495880 prefixEnd_7495880 := by exact prefixLift 7495880
  have htrace : WordTrace (prefixWord ++ tailWord_7495880) baseStart_7495880 baseEnd_7495880 := by
    simpa [prefixWord, tailWord_7495880, baseEnd_7495880] using wordTrace_append hprefix tailTrace_7495880
  have hstable : (prefixWord ++ tailWord_7495880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495880).length < 2 ^ (prefixWord ++ tailWord_7495880).sum := by decide
  have hdescent : baseEnd_7495880 < baseStart_7495880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495884 : List Nat := [2, 2, 1, 6, 1, 2, 9]
def baseStart_7495884 : Nat := 118140960795 + 7495884 * 2 ^ 59
def prefixEnd_7495884 : Nat := 4983230072969 + 3 ^ 40 * 7495884 * 2
def baseEnd_7495884 : Nat := 47518412621566117939223

theorem tailTrace_7495884 : CollatzResearch.WordTrace tailWord_7495884 prefixEnd_7495884 47518412621566117939223 := by
  unfold tailWord_7495884
  simp only [CollatzResearch.WordTrace]
  refine ⟨136698674987849968955387353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182264899983799958607183137 136698674987849968955387353)
  ·
    refine ⟨102524006240887476716540515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136698674987849968955387353 102524006240887476716540515)
    ·
      refine ⟨153786009361331215074810773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102524006240887476716540515 153786009361331215074810773)
      ·
        refine ⟨7208719188812400706631755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153786009361331215074810773 7208719188812400706631755)
        ·
          refine ⟨10813078783218601059947633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208719188812400706631755 10813078783218601059947633)
          ·
            refine ⟨8109809087413950794960725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10813078783218601059947633 8109809087413950794960725)
            ·
              refine ⟨47518412621566117939223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8109809087413950794960725 47518412621566117939223)
              ·
                rfl

theorem cell23_7495884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 9].length) (baseStart_7495884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495884 prefixEnd_7495884 := by exact prefixLift 7495884
  have htrace : WordTrace (prefixWord ++ tailWord_7495884) baseStart_7495884 baseEnd_7495884 := by
    simpa [prefixWord, tailWord_7495884, baseEnd_7495884] using wordTrace_append hprefix tailTrace_7495884
  have hstable : (prefixWord ++ tailWord_7495884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495884).length < 2 ^ (prefixWord ++ tailWord_7495884).sum := by decide
  have hdescent : baseEnd_7495884 < baseStart_7495884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495904 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2]
def baseStart_7495904 : Nat := 118140960795 + 7495904 * 2 ^ 59
def prefixEnd_7495904 : Nat := 4983230072969 + 3 ^ 40 * 7495904 * 2
def baseEnd_7495904 : Nat := 3849001691959945474826971

theorem tailTrace_7495904 : CollatzResearch.WordTrace tailWord_7495904 prefixEnd_7495904 3849001691959945474826971 := by
  unfold tailWord_7495904
  simp only [CollatzResearch.WordTrace]
  refine ⟨136699039717813740663251383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182265386290418320884335177 136699039717813740663251383)
  ·
    refine ⟨205048559576720610994877075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136699039717813740663251383 205048559576720610994877075)
    ·
      refine ⟨307572839365080916492315613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205048559576720610994877075 307572839365080916492315613)
      ·
        refine ⟨115339814761905343684618355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307572839365080916492315613 115339814761905343684618355)
        ·
          refine ⟨173009722142858015526927533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115339814761905343684618355 173009722142858015526927533)
          ·
            refine ⟨64878645803571755822597825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173009722142858015526927533 64878645803571755822597825)
            ·
              refine ⟨48658984352678816866948369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64878645803571755822597825 48658984352678816866948369)
              ·
                refine ⟨36494238264509112650211277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48658984352678816866948369 36494238264509112650211277)
                ·
                  refine ⟨13685339349190917243829229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36494238264509112650211277 13685339349190917243829229)
                  ·
                    refine ⟨5132002255946593966435961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13685339349190917243829229 5132002255946593966435961)
                    ·
                      refine ⟨3849001691959945474826971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132002255946593966435961 3849001691959945474826971)
                      ·
                        rfl

theorem cell23_7495904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_7495904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495904 prefixEnd_7495904 := by exact prefixLift 7495904
  have htrace : WordTrace (prefixWord ++ tailWord_7495904) baseStart_7495904 baseEnd_7495904 := by
    simpa [prefixWord, tailWord_7495904, baseEnd_7495904] using wordTrace_append hprefix tailTrace_7495904
  have hstable : (prefixWord ++ tailWord_7495904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495904).length < 2 ^ (prefixWord ++ tailWord_7495904).sum := by decide
  have hdescent : baseEnd_7495904 < baseStart_7495904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495921 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_7495921 : Nat := 118140960795 + 7495921 * 2 ^ 59
def prefixEnd_7495921 : Nat := 4983230072969 + 3 ^ 40 * 7495921 * 2
def baseEnd_7495921 : Nat := 3849010421131071908314393

theorem tailTrace_7495921 : CollatzResearch.WordTrace tailWord_7495921 prefixEnd_7495921 3849010421131071908314393 := by
  unfold tailWord_7495921
  simp only [CollatzResearch.WordTrace]
  refine ⟨273398699476565893229871617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182265799651043928819914411 273398699476565893229871617)
  ·
    refine ⟨205049024607424419922403713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273398699476565893229871617 205049024607424419922403713)
    ·
      refine ⟨153786768455568314941802785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205049024607424419922403713 153786768455568314941802785)
      ·
        refine ⟨115340076341676236206352089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153786768455568314941802785 115340076341676236206352089)
        ·
          refine ⟨86505057256257177154764067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115340076341676236206352089 86505057256257177154764067)
          ·
            refine ⟨129757585884385765732146101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86505057256257177154764067 129757585884385765732146101)
            ·
              refine ⟨12164773676661165537388697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129757585884385765732146101 12164773676661165537388697)
              ·
                refine ⟨9123580257495874153041523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12164773676661165537388697 9123580257495874153041523)
                ·
                  refine ⟨13685370386243811229562285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123580257495874153041523 13685370386243811229562285)
                  ·
                    refine ⟨5132013894841429211085857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13685370386243811229562285 5132013894841429211085857)
                    ·
                      refine ⟨3849010421131071908314393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132013894841429211085857 3849010421131071908314393)
                      ·
                        rfl

theorem cell23_7495921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_7495921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495921 prefixEnd_7495921 := by exact prefixLift 7495921
  have htrace : WordTrace (prefixWord ++ tailWord_7495921) baseStart_7495921 baseEnd_7495921 := by
    simpa [prefixWord, tailWord_7495921, baseEnd_7495921] using wordTrace_append hprefix tailTrace_7495921
  have hstable : (prefixWord ++ tailWord_7495921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495921).length < 2 ^ (prefixWord ++ tailWord_7495921).sum := by decide
  have hdescent : baseEnd_7495921 < baseStart_7495921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495937 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7495937 : Nat := 118140960795 + 7495937 * 2 ^ 59
def prefixEnd_7495937 : Nat := 4983230072969 + 3 ^ 40 * 7495937 * 2
def baseEnd_7495937 : Nat := 3849018636821543845714319

theorem tailTrace_7495937 : CollatzResearch.WordTrace tailWord_7495937 prefixEnd_7495937 3849018636821543845714319 := by
  unfold tailWord_7495937
  simp only [CollatzResearch.WordTrace]
  refine ⟨273399283044507927962454065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182266188696338618641636043 273399283044507927962454065)
  ·
    refine ⟨205049462283380945971840549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273399283044507927962454065 205049462283380945971840549)
    ·
      refine ⟨38446774178133927369720103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205049462283380945971840549 38446774178133927369720103)
      ·
        refine ⟨57670161267200891054580155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38446774178133927369720103 57670161267200891054580155)
        ·
          refine ⟨86505241900801336581870233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57670161267200891054580155 86505241900801336581870233)
          ·
            refine ⟨64878931425601002436402675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86505241900801336581870233 64878931425601002436402675)
            ·
              refine ⟨97318397138401503654604013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64878931425601002436402675 97318397138401503654604013)
              ·
                refine ⟨36494398926900563870476505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97318397138401503654604013 36494398926900563870476505)
                ·
                  refine ⟨27370799195175422902857379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36494398926900563870476505 27370799195175422902857379)
                  ·
                    refine ⟨41056198792763134354286069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27370799195175422902857379 41056198792763134354286069)
                    ·
                      refine ⟨3849018636821543845714319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41056198792763134354286069 3849018636821543845714319)
                      ·
                        rfl

theorem cell23_7495937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7495937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495937 prefixEnd_7495937 := by exact prefixLift 7495937
  have htrace : WordTrace (prefixWord ++ tailWord_7495937) baseStart_7495937 baseEnd_7495937 := by
    simpa [prefixWord, tailWord_7495937, baseEnd_7495937] using wordTrace_append hprefix tailTrace_7495937
  have hstable : (prefixWord ++ tailWord_7495937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495937).length < 2 ^ (prefixWord ++ tailWord_7495937).sum := by decide
  have hdescent : baseEnd_7495937 < baseStart_7495937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495947 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_7495947 : Nat := 118140960795 + 7495947 * 2 ^ 59
def prefixEnd_7495947 : Nat := 4983230072969 + 3 ^ 40 * 7495947 * 2
def baseEnd_7495947 : Nat := 3849023771628088806589273

theorem tailTrace_7495947 : CollatzResearch.WordTrace tailWord_7495947 prefixEnd_7495947 3849023771628088806589273 := by
  unfold tailWord_7495947
  simp only [CollatzResearch.WordTrace]
  refine ⟨273399647774471699670318095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182266431849647799780212063 273399647774471699670318095)
  ·
    refine ⟨410099471661707549505477143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273399647774471699670318095 410099471661707549505477143)
    ·
      refine ⟨615149207492561324258215715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410099471661707549505477143 615149207492561324258215715)
      ·
        refine ⟨922723811238841986387323573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615149207492561324258215715 922723811238841986387323573)
        ·
          refine ⟨86505357303641436223811585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 922723811238841986387323573 86505357303641436223811585)
          ·
            refine ⟨64879017977731077167858689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86505357303641436223811585 64879017977731077167858689)
            ·
              refine ⟨48659263483298307875894017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64879017977731077167858689 48659263483298307875894017)
              ·
                refine ⟨36494447612473730906920513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48659263483298307875894017 36494447612473730906920513)
                ·
                  refine ⟨27370835709355298180190385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36494447612473730906920513 27370835709355298180190385)
                  ·
                    refine ⟨20528126782016473635142789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27370835709355298180190385 20528126782016473635142789)
                    ·
                      refine ⟨3849023771628088806589273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20528126782016473635142789 3849023771628088806589273)
                      ·
                        rfl

theorem cell23_7495947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_7495947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495947 prefixEnd_7495947 := by exact prefixLift 7495947
  have htrace : WordTrace (prefixWord ++ tailWord_7495947) baseStart_7495947 baseEnd_7495947 := by
    simpa [prefixWord, tailWord_7495947, baseEnd_7495947] using wordTrace_append hprefix tailTrace_7495947
  have hstable : (prefixWord ++ tailWord_7495947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495947).length < 2 ^ (prefixWord ++ tailWord_7495947).sum := by decide
  have hdescent : baseEnd_7495947 < baseStart_7495947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495968 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7495968 : Nat := 118140960795 + 7495968 * 2 ^ 59
def prefixEnd_7495968 : Nat := 4983230072969 + 3 ^ 40 * 7495968 * 2
def baseEnd_7495968 : Nat := 3849034554721833224426677

theorem tailTrace_7495968 : CollatzResearch.WordTrace tailWord_7495968 prefixEnd_7495968 3849034554721833224426677 := by
  unfold tailWord_7495968
  simp only [CollatzResearch.WordTrace]
  refine ⟨136700206853697810128416279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182266942471597080171221705 136700206853697810128416279)
  ·
    refine ⟨205050310280546715192624419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136700206853697810128416279 205050310280546715192624419)
    ·
      refine ⟨307575465420820072788936629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205050310280546715192624419 307575465420820072788936629)
      ·
        refine ⟨28835199883201881823962809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307575465420820072788936629 28835199883201881823962809)
        ·
          refine ⟨21626399912401411367972107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28835199883201881823962809 21626399912401411367972107)
          ·
            refine ⟨32439599868602117051958161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21626399912401411367972107 32439599868602117051958161)
            ·
              refine ⟨24329699901451587788968621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32439599868602117051958161 24329699901451587788968621)
              ·
                refine ⟨9123637463044345420863233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24329699901451587788968621 9123637463044345420863233)
                ·
                  refine ⟨6842728097283259065647425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123637463044345420863233 6842728097283259065647425)
                  ·
                    refine ⟨5132046072962444299235569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842728097283259065647425 5132046072962444299235569)
                    ·
                      refine ⟨3849034554721833224426677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132046072962444299235569 3849034554721833224426677)
                      ·
                        rfl

theorem cell23_7495968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7495968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495968 prefixEnd_7495968 := by exact prefixLift 7495968
  have htrace : WordTrace (prefixWord ++ tailWord_7495968) baseStart_7495968 baseEnd_7495968 := by
    simpa [prefixWord, tailWord_7495968, baseEnd_7495968] using wordTrace_append hprefix tailTrace_7495968
  have hstable : (prefixWord ++ tailWord_7495968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495968).length < 2 ^ (prefixWord ++ tailWord_7495968).sum := by decide
  have hdescent : baseEnd_7495968 < baseStart_7495968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7495987 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 7]
def baseStart_7495987 : Nat := 118140960795 + 7495987 * 2 ^ 59
def prefixEnd_7495987 : Nat := 4983230072969 + 3 ^ 40 * 7495987 * 2
def baseEnd_7495987 : Nat := 1283014770284756216696363

theorem tailTrace_7495987 : CollatzResearch.WordTrace tailWord_7495987 prefixEnd_7495987 1283014770284756216696363 := by
  unfold tailWord_7495987
  simp only [CollatzResearch.WordTrace]
  refine ⟨273401106694326786501774215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182267404462884524334516143 273401106694326786501774215)
  ·
    refine ⟨410101660041490179752661323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273401106694326786501774215 410101660041490179752661323)
    ·
      refine ⟨615152490062235269628991985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410101660041490179752661323 615152490062235269628991985)
      ·
        refine ⟨461364367546676452221743989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615152490062235269628991985 461364367546676452221743989)
        ·
          refine ⟨43252909457500917395788499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461364367546676452221743989 43252909457500917395788499)
          ·
            refine ⟨64879364186251376093682749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43252909457500917395788499 64879364186251376093682749)
            ·
              refine ⟨24329761569844266035131031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64879364186251376093682749 24329761569844266035131031)
              ·
                refine ⟨36494642354766399052696547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24329761569844266035131031 36494642354766399052696547)
                ·
                  refine ⟨54741963532149598579044821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36494642354766399052696547 54741963532149598579044821)
                  ·
                    refine ⟨1283014770284756216696363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54741963532149598579044821 1283014770284756216696363)
                    ·
                      rfl

theorem cell23_7495987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_7495987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7495987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7495987 prefixEnd_7495987 := by exact prefixLift 7495987
  have htrace : WordTrace (prefixWord ++ tailWord_7495987) baseStart_7495987 baseEnd_7495987 := by
    simpa [prefixWord, tailWord_7495987, baseEnd_7495987] using wordTrace_append hprefix tailTrace_7495987
  have hstable : (prefixWord ++ tailWord_7495987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7495987).length < 2 ^ (prefixWord ++ tailWord_7495987).sum := by decide
  have hdescent : baseEnd_7495987 < baseStart_7495987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7495987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496024 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_7496024 : Nat := 118140960795 + 7496024 * 2 ^ 59
def prefixEnd_7496024 : Nat := 4983230072969 + 3 ^ 40 * 7496024 * 2
def baseEnd_7496024 : Nat := 3849063309638485005326419

theorem tailTrace_7496024 : CollatzResearch.WordTrace tailWord_7496024 prefixEnd_7496024 3849063309638485005326419 := by
  unfold tailWord_7496024
  simp only [CollatzResearch.WordTrace]
  refine ⟨136701228097596370910435563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182268304130128494547247417 136701228097596370910435563)
  ·
    refine ⟨205051842146394556365653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136701228097596370910435563 205051842146394556365653345)
    ·
      refine ⟨153788881609795917274240009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205051842146394556365653345 153788881609795917274240009)
      ·
        refine ⟨115341661207346937955680007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153788881609795917274240009 115341661207346937955680007)
        ·
          refine ⟨173012491811020406933520011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115341661207346937955680007 173012491811020406933520011)
          ·
            refine ⟨259518737716530610400280017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173012491811020406933520011 259518737716530610400280017)
            ·
              refine ⟨194639053287397957800210013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259518737716530610400280017 194639053287397957800210013)
              ·
                refine ⟨72989644982774234175078755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194639053287397957800210013 72989644982774234175078755)
                ·
                  refine ⟨109484467474161351262618133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72989644982774234175078755 109484467474161351262618133)
                  ·
                    refine ⟨5132084412851313340435225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109484467474161351262618133 5132084412851313340435225)
                    ·
                      refine ⟨3849063309638485005326419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132084412851313340435225 3849063309638485005326419)
                      ·
                        rfl

theorem cell23_7496024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_7496024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496024 prefixEnd_7496024 := by exact prefixLift 7496024
  have htrace : WordTrace (prefixWord ++ tailWord_7496024) baseStart_7496024 baseEnd_7496024 := by
    simpa [prefixWord, tailWord_7496024, baseEnd_7496024] using wordTrace_append hprefix tailTrace_7496024
  have hstable : (prefixWord ++ tailWord_7496024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496024).length < 2 ^ (prefixWord ++ tailWord_7496024).sum := by decide
  have hdescent : baseEnd_7496024 < baseStart_7496024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496061 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_7496061 : Nat := 118140960795 + 7496061 * 2 ^ 59
def prefixEnd_7496061 : Nat := 4983230072969 + 3 ^ 40 * 7496061 * 2
def baseEnd_7496061 : Nat := 3849082308422701360563749

theorem tailTrace_7496061 : CollatzResearch.WordTrace tailWord_7496061 prefixEnd_7496061 3849082308422701360563749 := by
  unfold tailWord_7496061
  simp only [CollatzResearch.WordTrace]
  refine ⟨273403805696058697139968037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182269203797372464759978691 273403805696058697139968037)
  ·
    refine ⟨51263213568011005713744007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273403805696058697139968037 51263213568011005713744007)
    ·
      refine ⟨76894820352016508570616011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51263213568011005713744007 76894820352016508570616011)
      ·
        refine ⟨115342230528024762855924017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76894820352016508570616011 115342230528024762855924017)
        ·
          refine ⟨86506672896018572141943013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115342230528024762855924017 86506672896018572141943013)
          ·
            refine ⟨16220001168003482276614315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86506672896018572141943013 16220001168003482276614315)
            ·
              refine ⟨24330001752005223414921473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16220001168003482276614315 24330001752005223414921473)
              ·
                refine ⟨18247501314003917561191105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24330001752005223414921473 18247501314003917561191105)
                ·
                  refine ⟨13685625985502938170893329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18247501314003917561191105 13685625985502938170893329)
                  ·
                    refine ⟨10264219489127203628169997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13685625985502938170893329 10264219489127203628169997)
                    ·
                      refine ⟨3849082308422701360563749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264219489127203628169997 3849082308422701360563749)
                      ·
                        rfl

theorem cell23_7496061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_7496061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496061 prefixEnd_7496061 := by exact prefixLift 7496061
  have htrace : WordTrace (prefixWord ++ tailWord_7496061) baseStart_7496061 baseEnd_7496061 := by
    simpa [prefixWord, tailWord_7496061, baseEnd_7496061] using wordTrace_append hprefix tailTrace_7496061
  have hstable : (prefixWord ++ tailWord_7496061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496061).length < 2 ^ (prefixWord ++ tailWord_7496061).sum := by decide
  have hdescent : baseEnd_7496061 < baseStart_7496061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_7496108 : Nat := 118140960795 + 7496108 * 2 ^ 59
def prefixEnd_7496108 : Nat := 4983230072969 + 3 ^ 40 * 7496108 * 2
def baseEnd_7496108 : Nat := 3849106442013462676676033

theorem tailTrace_7496108 : CollatzResearch.WordTrace tailWord_7496108 prefixEnd_7496108 3849106442013462676676033 := by
  unfold tailWord_7496108
  simp only [CollatzResearch.WordTrace]
  refine ⟨136702759963444212083464489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182270346617925616111285985 136702759963444212083464489)
  ·
    refine ⟨102527069972583159062598367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136702759963444212083464489 102527069972583159062598367)
    ·
      refine ⟨153790604958874738593897551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102527069972583159062598367 153790604958874738593897551)
      ·
        refine ⟨230685907438312107890846327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153790604958874738593897551 230685907438312107890846327)
        ·
          refine ⟨346028861157468161836269491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230685907438312107890846327 346028861157468161836269491)
          ·
            refine ⟨519043291736202242754404237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346028861157468161836269491 519043291736202242754404237)
            ·
              refine ⟨194641234401075841032901589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519043291736202242754404237 194641234401075841032901589)
              ·
                refine ⟨4561903931275215024208631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194641234401075841032901589 4561903931275215024208631)
                ·
                  refine ⟨6842855896912822536312947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561903931275215024208631 6842855896912822536312947)
                  ·
                    refine ⟨10264283845369233804469421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6842855896912822536312947 10264283845369233804469421)
                    ·
                      refine ⟨3849106442013462676676033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264283845369233804469421 3849106442013462676676033)
                      ·
                        rfl

theorem cell23_7496108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_7496108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496108 prefixEnd_7496108 := by exact prefixLift 7496108
  have htrace : WordTrace (prefixWord ++ tailWord_7496108) baseStart_7496108 baseEnd_7496108 := by
    simpa [prefixWord, tailWord_7496108, baseEnd_7496108] using wordTrace_append hprefix tailTrace_7496108
  have hstable : (prefixWord ++ tailWord_7496108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496108).length < 2 ^ (prefixWord ++ tailWord_7496108).sum := by decide
  have hdescent : baseEnd_7496108 < baseStart_7496108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496125 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7496125 : Nat := 118140960795 + 7496125 * 2 ^ 59
def prefixEnd_7496125 : Nat := 4983230072969 + 3 ^ 40 * 7496125 * 2
def baseEnd_7496125 : Nat := 3849115171184589110163455

theorem tailTrace_7496125 : CollatzResearch.WordTrace tailWord_7496125 prefixEnd_7496125 3849115171184589110163455 := by
  unfold tailWord_7496125
  simp only [CollatzResearch.WordTrace]
  refine ⟨273406139967826836070297829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182270759978551224046865219 273406139967826836070297829)
  ·
    refine ⟨51263651243967531763180843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273406139967826836070297829 51263651243967531763180843)
    ·
      refine ⟨76895476865951297644771265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51263651243967531763180843 76895476865951297644771265)
      ·
        refine ⟨57671607649463473233578449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76895476865951297644771265 57671607649463473233578449)
        ·
          refine ⟨43253705737097604925183837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57671607649463473233578449 43253705737097604925183837)
          ·
            refine ⟨16220139651411601846943939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43253705737097604925183837 16220139651411601846943939)
            ·
              refine ⟨24330209477117402770415909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16220139651411601846943939 24330209477117402770415909)
              ·
                refine ⟨4561914276959513019452983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24330209477117402770415909 4561914276959513019452983)
                ·
                  refine ⟨6842871415439269529179475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561914276959513019452983 6842871415439269529179475)
                  ·
                    refine ⟨10264307123158904293769213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6842871415439269529179475 10264307123158904293769213)
                    ·
                      refine ⟨3849115171184589110163455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264307123158904293769213 3849115171184589110163455)
                      ·
                        rfl

theorem cell23_7496125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7496125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496125 prefixEnd_7496125 := by exact prefixLift 7496125
  have htrace : WordTrace (prefixWord ++ tailWord_7496125) baseStart_7496125 baseEnd_7496125 := by
    simpa [prefixWord, tailWord_7496125, baseEnd_7496125] using wordTrace_append hprefix tailTrace_7496125
  have hstable : (prefixWord ++ tailWord_7496125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496125).length < 2 ^ (prefixWord ++ tailWord_7496125).sum := by decide
  have hdescent : baseEnd_7496125 < baseStart_7496125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496168 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7496168 : Nat := 118140960795 + 7496168 * 2 ^ 59
def prefixEnd_7496168 : Nat := 4983230072969 + 3 ^ 40 * 7496168 * 2
def baseEnd_7496168 : Nat := 3849137250852732441925757

theorem tailTrace_7496168 : CollatzResearch.WordTrace tailWord_7496168 prefixEnd_7496168 3849137250852732441925757 := by
  unfold tailWord_7496168
  simp only [CollatzResearch.WordTrace]
  refine ⟨136703854153335527207056579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182271805537780702942742105 136703854153335527207056579)
  ·
    refine ⟨205055781230003290810584869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136703854153335527207056579 205055781230003290810584869)
    ·
      refine ⟨38447958980625617026984663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205055781230003290810584869 38447958980625617026984663)
      ·
        refine ⟨57671938470938425540476995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38447958980625617026984663 57671938470938425540476995)
        ·
          refine ⟨86507907706407638310715493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57671938470938425540476995 86507907706407638310715493)
          ·
            refine ⟨16220232694951432183259155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86507907706407638310715493 16220232694951432183259155)
            ·
              refine ⟨24330349042427148274888733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16220232694951432183259155 24330349042427148274888733)
              ·
                refine ⟨9123880890910180603083275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24330349042427148274888733 9123880890910180603083275)
                ·
                  refine ⟨13685821336365270904624913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123880890910180603083275 13685821336365270904624913)
                  ·
                    refine ⟨10264366002273953178468685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13685821336365270904624913 10264366002273953178468685)
                    ·
                      refine ⟨3849137250852732441925757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264366002273953178468685 3849137250852732441925757)
                      ·
                        rfl

theorem cell23_7496168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7496168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496168 prefixEnd_7496168 := by exact prefixLift 7496168
  have htrace : WordTrace (prefixWord ++ tailWord_7496168) baseStart_7496168 baseEnd_7496168 := by
    simpa [prefixWord, tailWord_7496168, baseEnd_7496168] using wordTrace_append hprefix tailTrace_7496168
  have hstable : (prefixWord ++ tailWord_7496168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496168).length < 2 ^ (prefixWord ++ tailWord_7496168).sum := by decide
  have hdescent : baseEnd_7496168 < baseStart_7496168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496182 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7496182 : Nat := 118140960795 + 7496182 * 2 ^ 59
def prefixEnd_7496182 : Nat := 4983230072969 + 3 ^ 40 * 7496182 * 2
def baseEnd_7496182 : Nat := 3849144439581895387150693

theorem tailTrace_7496182 : CollatzResearch.WordTrace tailWord_7496182 prefixEnd_7496182 3849144439581895387150693 := by
  unfold tailWord_7496182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17088013683038770925320175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182272145952413556536748533 17088013683038770925320175)
  ·
    refine ⟨25632020524558156387980263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17088013683038770925320175 25632020524558156387980263)
    ·
      refine ⟨38448030786837234581970395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25632020524558156387980263 38448030786837234581970395)
      ·
        refine ⟨57672046180255851872955593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38448030786837234581970395 57672046180255851872955593)
        ·
          refine ⟨43254034635191888904716695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57672046180255851872955593 43254034635191888904716695)
          ·
            refine ⟨64881051952787833357075043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43254034635191888904716695 64881051952787833357075043)
            ·
              refine ⟨97321577929181750035612565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64881051952787833357075043 97321577929181750035612565)
              ·
                refine ⟨4561948965430394532919339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97321577929181750035612565 4561948965430394532919339)
                ·
                  refine ⟨6842923448145591799379009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561948965430394532919339 6842923448145591799379009)
                  ·
                    refine ⟨5132192586109193849534257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842923448145591799379009 5132192586109193849534257)
                    ·
                      refine ⟨3849144439581895387150693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132192586109193849534257 3849144439581895387150693)
                      ·
                        rfl

theorem cell23_7496182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7496182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496182 prefixEnd_7496182 := by exact prefixLift 7496182
  have htrace : WordTrace (prefixWord ++ tailWord_7496182) baseStart_7496182 baseEnd_7496182 := by
    simpa [prefixWord, tailWord_7496182, baseEnd_7496182] using wordTrace_append hprefix tailTrace_7496182
  have hstable : (prefixWord ++ tailWord_7496182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496182).length < 2 ^ (prefixWord ++ tailWord_7496182).sum := by decide
  have hdescent : baseEnd_7496182 < baseStart_7496182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496205 : List Nat := [1, 7, 1, 1, 1, 1, 4, 7]
def baseStart_7496205 : Nat := 118140960795 + 7496205 * 2 ^ 59
def prefixEnd_7496205 : Nat := 4983230072969 + 3 ^ 40 * 7496205 * 2
def baseEnd_7496205 : Nat := 142561342579146251746781

theorem tailTrace_7496205 : CollatzResearch.WordTrace tailWord_7496205 prefixEnd_7496205 142561342579146251746781 := by
  unfold tailWord_7496205
  simp only [CollatzResearch.WordTrace]
  refine ⟨273409057807537009733210069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182272705205024673155473379 273409057807537009733210069)
  ·
    refine ⟨6408024792364148665622111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 273409057807537009733210069 6408024792364148665622111)
    ·
      refine ⟨9612037188546222998433167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408024792364148665622111 9612037188546222998433167)
      ·
        refine ⟨14418055782819334497649751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612037188546222998433167 14418055782819334497649751)
        ·
          refine ⟨21627083674229001746474627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418055782819334497649751 21627083674229001746474627)
          ·
            refine ⟨32440625511343502619711941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21627083674229001746474627 32440625511343502619711941)
            ·
              refine ⟨6082617283376906741195989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32440625511343502619711941 6082617283376906741195989)
              ·
                refine ⟨142561342579146251746781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6082617283376906741195989 142561342579146251746781)
                ·
                  rfl

theorem cell23_7496205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 7].length) (baseStart_7496205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496205 prefixEnd_7496205 := by exact prefixLift 7496205
  have htrace : WordTrace (prefixWord ++ tailWord_7496205) baseStart_7496205 baseEnd_7496205 := by
    simpa [prefixWord, tailWord_7496205, baseEnd_7496205] using wordTrace_append hprefix tailTrace_7496205
  have hstable : (prefixWord ++ tailWord_7496205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496205).length < 2 ^ (prefixWord ++ tailWord_7496205).sum := by decide
  have hdescent : baseEnd_7496205 < baseStart_7496205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496255 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 2, 2, 2]
def baseStart_7496255 : Nat := 118140960795 + 7496255 * 2 ^ 59
def prefixEnd_7496255 : Nat := 4983230072969 + 3 ^ 40 * 7496255 * 2
def baseEnd_7496255 : Nat := 3849181923669673601537857

theorem tailTrace_7496255 : CollatzResearch.WordTrace tailWord_7496255 prefixEnd_7496255 3849181923669673601537857 := by
  unfold tailWord_7496255
  simp only [CollatzResearch.WordTrace]
  refine ⟨273410881457355868272530219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182273920971570578848353479 273410881457355868272530219)
  ·
    refine ⟨410116322186033802408795329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273410881457355868272530219 410116322186033802408795329)
    ·
      refine ⟨307587241639525351806596497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410116322186033802408795329 307587241639525351806596497)
      ·
        refine ⟨230690431229644013854947373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307587241639525351806596497 230690431229644013854947373)
        ·
          refine ⟨86508911711116505195605265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230690431229644013854947373 86508911711116505195605265)
          ·
            refine ⟨64881683783337378896703949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86508911711116505195605265 64881683783337378896703949)
            ·
              refine ⟨24330631418751517086263981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64881683783337378896703949 24330631418751517086263981)
              ·
                refine ⟨9123986782031818907348993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24330631418751517086263981 9123986782031818907348993)
                ·
                  refine ⟨6842990086523864180511745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123986782031818907348993 6842990086523864180511745)
                  ·
                    refine ⟨5132242564892898135383809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842990086523864180511745 5132242564892898135383809)
                    ·
                      refine ⟨3849181923669673601537857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132242564892898135383809 3849181923669673601537857)
                      ·
                        rfl

theorem cell23_7496255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_7496255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496255 prefixEnd_7496255 := by exact prefixLift 7496255
  have htrace : WordTrace (prefixWord ++ tailWord_7496255) baseStart_7496255 baseEnd_7496255 := by
    simpa [prefixWord, tailWord_7496255, baseEnd_7496255] using wordTrace_append hprefix tailTrace_7496255
  have hstable : (prefixWord ++ tailWord_7496255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496255).length < 2 ^ (prefixWord ++ tailWord_7496255).sum := by decide
  have hdescent : baseEnd_7496255 < baseStart_7496255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_7496264 : Nat := 118140960795 + 7496264 * 2 ^ 59
def prefixEnd_7496264 : Nat := 4983230072969 + 3 ^ 40 * 7496264 * 2
def baseEnd_7496264 : Nat := 3849186544995564066325315

theorem tailTrace_7496264 : CollatzResearch.WordTrace tailWord_7496264 prefixEnd_7496264 3849186544995564066325315 := by
  unfold tailWord_7496264
  simp only [CollatzResearch.WordTrace]
  refine ⟨136705604857161631404803923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182274139809548841873071897 136705604857161631404803923)
  ·
    refine ⟨205058407285742447107205885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136705604857161631404803923 205058407285742447107205885)
    ·
      refine ⟨76896902732153417665202207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205058407285742447107205885 76896902732153417665202207)
      ·
        refine ⟨115345354098230126497803311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76896902732153417665202207 115345354098230126497803311)
        ·
          refine ⟨173018031147345189746704967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115345354098230126497803311 173018031147345189746704967)
          ·
            refine ⟨259527046721017784620057451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173018031147345189746704967 259527046721017784620057451)
            ·
              refine ⟨389290570081526676930086177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259527046721017784620057451 389290570081526676930086177)
              ·
                refine ⟨291967927561145007697564633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389290570081526676930086177 291967927561145007697564633)
                ·
                  refine ⟨218975945670858755773173475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291967927561145007697564633 218975945670858755773173475)
                  ·
                    refine ⟨328463918506288133659760213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218975945670858755773173475 328463918506288133659760213)
                    ·
                      refine ⟨3849186544995564066325315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328463918506288133659760213 3849186544995564066325315)
                      ·
                        rfl

theorem cell23_7496264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_7496264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496264 prefixEnd_7496264 := by exact prefixLift 7496264
  have htrace : WordTrace (prefixWord ++ tailWord_7496264) baseStart_7496264 baseEnd_7496264 := by
    simpa [prefixWord, tailWord_7496264, baseEnd_7496264] using wordTrace_append hprefix tailTrace_7496264
  have hstable : (prefixWord ++ tailWord_7496264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496264).length < 2 ^ (prefixWord ++ tailWord_7496264).sum := by decide
  have hdescent : baseEnd_7496264 < baseStart_7496264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496291 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 2, 5]
def baseStart_7496291 : Nat := 118140960795 + 7496291 * 2 ^ 59
def prefixEnd_7496291 : Nat := 4983230072969 + 3 ^ 40 * 7496291 * 2
def baseEnd_7496291 : Nat := 1283066802991078486895897

theorem tailTrace_7496291 : CollatzResearch.WordTrace tailWord_7496291 prefixEnd_7496291 1283066802991078486895897 := by
  unfold tailWord_7496291
  simp only [CollatzResearch.WordTrace]
  refine ⟨273412194485225446420840727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182274796323483630947227151 273412194485225446420840727)
  ·
    refine ⟨410118291727838169631261091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273412194485225446420840727 410118291727838169631261091)
    ·
      refine ⟨615177437591757254446891637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410118291727838169631261091 615177437591757254446891637)
      ·
        refine ⟨57672884774227242604396091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 615177437591757254446891637 57672884774227242604396091)
        ·
          refine ⟨86509327161340863906594137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57672884774227242604396091 86509327161340863906594137)
          ·
            refine ⟨64881995371005647929945603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86509327161340863906594137 64881995371005647929945603)
            ·
              refine ⟨97322993056508471894918405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64881995371005647929945603 97322993056508471894918405)
              ·
                refine ⟨18248061198095338480297201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97322993056508471894918405 18248061198095338480297201)
                ·
                  refine ⟨13686045898571503860222901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18248061198095338480297201 13686045898571503860222901)
                  ·
                    refine ⟨1283066802991078486895897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13686045898571503860222901 1283066802991078486895897)
                    ·
                      rfl

theorem cell23_7496291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].length) (baseStart_7496291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496291 prefixEnd_7496291 := by exact prefixLift 7496291
  have htrace : WordTrace (prefixWord ++ tailWord_7496291) baseStart_7496291 baseEnd_7496291 := by
    simpa [prefixWord, tailWord_7496291, baseEnd_7496291] using wordTrace_append hprefix tailTrace_7496291
  have hstable : (prefixWord ++ tailWord_7496291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496291).length < 2 ^ (prefixWord ++ tailWord_7496291).sum := by decide
  have hdescent : baseEnd_7496291 < baseStart_7496291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496298 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_7496298 : Nat := 118140960795 + 7496298 * 2 ^ 59
def prefixEnd_7496298 : Nat := 4983230072969 + 3 ^ 40 * 7496298 * 2
def baseEnd_7496298 : Nat := 3849204003337816933300159

theorem tailTrace_7496298 : CollatzResearch.WordTrace tailWord_7496298 prefixEnd_7496298 3849204003337816933300159 := by
  unfold tailWord_7496298
  simp only [CollatzResearch.WordTrace]
  refine ⟨68353112449050021654086387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182274966530800057744230365 68353112449050021654086387)
  ·
    refine ⟨102529668673575032481129581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68353112449050021654086387 102529668673575032481129581)
    ·
      refine ⟨38448625752590637180423593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102529668673575032481129581 38448625752590637180423593)
      ·
        refine ⟨28836469314442977885317695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38448625752590637180423593 28836469314442977885317695)
        ·
          refine ⟨43254703971664466827976543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28836469314442977885317695 43254703971664466827976543)
          ·
            refine ⟨64882055957496700241964815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43254703971664466827976543 64882055957496700241964815)
            ·
              refine ⟨97323083936245050362947223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64882055957496700241964815 97323083936245050362947223)
              ·
                refine ⟨145984625904367575544420835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97323083936245050362947223 145984625904367575544420835)
                ·
                  refine ⟨218976938856551363316631253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145984625904367575544420835 218976938856551363316631253)
                  ·
                    refine ⟨5132272004450422577733545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 218976938856551363316631253 5132272004450422577733545)
                    ·
                      refine ⟨3849204003337816933300159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132272004450422577733545 3849204003337816933300159)
                      ·
                        rfl

theorem cell23_7496298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_7496298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496298 prefixEnd_7496298 := by exact prefixLift 7496298
  have htrace : WordTrace (prefixWord ++ tailWord_7496298) baseStart_7496298 baseEnd_7496298 := by
    simpa [prefixWord, tailWord_7496298, baseEnd_7496298] using wordTrace_append hprefix tailTrace_7496298
  have hstable : (prefixWord ++ tailWord_7496298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496298).length < 2 ^ (prefixWord ++ tailWord_7496298).sum := by decide
  have hdescent : baseEnd_7496298 < baseStart_7496298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496311 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_7496311 : Nat := 118140960795 + 7496311 * 2 ^ 59
def prefixEnd_7496311 : Nat := 4983230072969 + 3 ^ 40 * 7496311 * 2
def baseEnd_7496311 : Nat := 3849210678586325382437599

theorem tailTrace_7496311 : CollatzResearch.WordTrace tailWord_7496311 prefixEnd_7496311 3849210678586325382437599 := by
  unfold tailWord_7496311
  simp only [CollatzResearch.WordTrace]
  refine ⟨273412923945152989836568787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182275282630101993224379191 273412923945152989836568787)
  ·
    refine ⟨410119385917729484754853181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273412923945152989836568787 410119385917729484754853181)
    ·
      refine ⟨153794769719148556783069943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410119385917729484754853181 153794769719148556783069943)
      ·
        refine ⟨230692154578722835174604915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153794769719148556783069943 230692154578722835174604915)
        ·
          refine ⟨346038231868084252761907373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230692154578722835174604915 346038231868084252761907373)
          ·
            refine ⟨129764336950531594785715265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346038231868084252761907373 129764336950531594785715265)
            ·
              refine ⟨97323252712898696089286449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129764336950531594785715265 97323252712898696089286449)
              ·
                refine ⟨72992439534674022066964837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97323252712898696089286449 72992439534674022066964837)
                ·
                  refine ⟨13686082412751379137555907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72992439534674022066964837 13686082412751379137555907)
                  ·
                    refine ⟨20529123619127068706333861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13686082412751379137555907 20529123619127068706333861)
                    ·
                      refine ⟨3849210678586325382437599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20529123619127068706333861 3849210678586325382437599)
                      ·
                        rfl

theorem cell23_7496311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_7496311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496311 prefixEnd_7496311 := by exact prefixLift 7496311
  have htrace : WordTrace (prefixWord ++ tailWord_7496311) baseStart_7496311 baseEnd_7496311 := by
    simpa [prefixWord, tailWord_7496311, baseEnd_7496311] using wordTrace_append hprefix tailTrace_7496311
  have hstable : (prefixWord ++ tailWord_7496311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496311).length < 2 ^ (prefixWord ++ tailWord_7496311).sum := by decide
  have hdescent : baseEnd_7496311 < baseStart_7496311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496361 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_7496361 : Nat := 118140960795 + 7496361 * 2 ^ 59
def prefixEnd_7496361 : Nat := 4983230072969 + 3 ^ 40 * 7496361 * 2
def baseEnd_7496361 : Nat := 3849236352619050186812369

theorem tailTrace_7496361 : CollatzResearch.WordTrace tailWord_7496361 prefixEnd_7496361 3849236352619050186812369 := by
  unfold tailWord_7496361
  simp only [CollatzResearch.WordTrace]
  refine ⟨273414747594971848375888937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182276498396647898917259291 273414747594971848375888937)
  ·
    refine ⟨205061060696228886281916703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273414747594971848375888937 205061060696228886281916703)
    ·
      refine ⟨307591591044343329422875055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205061060696228886281916703 307591591044343329422875055)
      ·
        refine ⟨461387386566514994134312583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307591591044343329422875055 461387386566514994134312583)
        ·
          refine ⟨692081079849772491201468875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461387386566514994134312583 692081079849772491201468875)
          ·
            refine ⟨1038121619774658736802203313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692081079849772491201468875 1038121619774658736802203313)
            ·
              refine ⟨778591214830994052601652485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038121619774658736802203313 778591214830994052601652485)
              ·
                refine ⟨145985852780811384862809841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778591214830994052601652485 145985852780811384862809841)
                ·
                  refine ⟨109489389585608538647107381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145985852780811384862809841 109489389585608538647107381)
                  ·
                    refine ⟨10264630273650800498166317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109489389585608538647107381 10264630273650800498166317)
                    ·
                      refine ⟨3849236352619050186812369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264630273650800498166317 3849236352619050186812369)
                      ·
                        rfl

theorem cell23_7496361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_7496361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496361 prefixEnd_7496361 := by exact prefixLift 7496361
  have htrace : WordTrace (prefixWord ++ tailWord_7496361) baseStart_7496361 baseEnd_7496361 := by
    simpa [prefixWord, tailWord_7496361, baseEnd_7496361] using wordTrace_append hprefix tailTrace_7496361
  have hstable : (prefixWord ++ tailWord_7496361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496361).length < 2 ^ (prefixWord ++ tailWord_7496361).sum := by decide
  have hdescent : baseEnd_7496361 < baseStart_7496361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496435 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 5, 2, 2]
def baseStart_7496435 : Nat := 118140960795 + 7496435 * 2 ^ 59
def prefixEnd_7496435 : Nat := 4983230072969 + 3 ^ 40 * 7496435 * 2
def baseEnd_7496435 : Nat := 3849274350187482897287029

theorem tailTrace_7496435 : CollatzResearch.WordTrace tailWord_7496435 prefixEnd_7496435 3849274350187482897287029 := by
  unfold tailWord_7496435
  simp only [CollatzResearch.WordTrace]
  refine ⟨273417446596703759014082759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182278297731135839342721839 273417446596703759014082759)
  ·
    refine ⟨410126169895055638521124139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273417446596703759014082759 410126169895055638521124139)
    ·
      refine ⟨615189254842583457781686209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410126169895055638521124139 615189254842583457781686209)
      ·
        refine ⟨461391941131937593336264657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615189254842583457781686209 461391941131937593336264657)
        ·
          refine ⟨346043955848953195002198493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461391941131937593336264657 346043955848953195002198493)
          ·
            refine ⟨129766483443357448125824435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346043955848953195002198493 129766483443357448125824435)
            ·
              refine ⟨194649725165036172188736653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129766483443357448125824435 194649725165036172188736653)
              ·
                refine ⟨72993646936888564570776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194649725165036172188736653 72993646936888564570776245)
                ·
                  refine ⟨6843154400333302928510273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72993646936888564570776245 6843154400333302928510273)
                  ·
                    refine ⟨5132365800249977196382705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6843154400333302928510273 5132365800249977196382705)
                    ·
                      refine ⟨3849274350187482897287029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132365800249977196382705 3849274350187482897287029)
                      ·
                        rfl

theorem cell23_7496435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2, 2].length) (baseStart_7496435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496435 prefixEnd_7496435 := by exact prefixLift 7496435
  have htrace : WordTrace (prefixWord ++ tailWord_7496435) baseStart_7496435 baseEnd_7496435 := by
    simpa [prefixWord, tailWord_7496435, baseEnd_7496435] using wordTrace_append hprefix tailTrace_7496435
  have hstable : (prefixWord ++ tailWord_7496435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496435).length < 2 ^ (prefixWord ++ tailWord_7496435).sum := by decide
  have hdescent : baseEnd_7496435 < baseStart_7496435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496452 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_7496452 : Nat := 118140960795 + 7496452 * 2 ^ 59
def prefixEnd_7496452 : Nat := 4983230072969 + 3 ^ 40 * 7496452 * 2
def baseEnd_7496452 : Nat := 3849283079358609330774451

theorem tailTrace_7496452 : CollatzResearch.WordTrace tailWord_7496452 prefixEnd_7496452 3849283079358609330774451 := by
  unfold tailWord_7496452
  simp only [CollatzResearch.WordTrace]
  refine ⟨136709033318821085458725805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182278711091761447278301073 136709033318821085458725805)
  ·
    refine ⟨51265887494557907047022177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136709033318821085458725805 51265887494557907047022177)
    ·
      refine ⟨38449415620918430285266633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51265887494557907047022177 38449415620918430285266633)
      ·
        refine ⟨28837061715688822713949975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38449415620918430285266633 28837061715688822713949975)
        ·
          refine ⟨43255592573533234070924963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28837061715688822713949975 43255592573533234070924963)
          ·
            refine ⟨64883388860299851106387445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43255592573533234070924963 64883388860299851106387445)
            ·
              refine ⟨6082817705653111041223823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64883388860299851106387445 6082817705653111041223823)
              ·
                refine ⟨9124226558479666561835735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082817705653111041223823 9124226558479666561835735)
                ·
                  refine ⟨13686339837719499842753603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124226558479666561835735 13686339837719499842753603)
                  ·
                    refine ⟨20529509756579249764130405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13686339837719499842753603 20529509756579249764130405)
                    ·
                      refine ⟨3849283079358609330774451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20529509756579249764130405 3849283079358609330774451)
                      ·
                        rfl

theorem cell23_7496452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_7496452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496452 prefixEnd_7496452 := by exact prefixLift 7496452
  have htrace : WordTrace (prefixWord ++ tailWord_7496452) baseStart_7496452 baseEnd_7496452 := by
    simpa [prefixWord, tailWord_7496452, baseEnd_7496452] using wordTrace_append hprefix tailTrace_7496452
  have hstable : (prefixWord ++ tailWord_7496452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496452).length < 2 ^ (prefixWord ++ tailWord_7496452).sum := by decide
  have hdescent : baseEnd_7496452 < baseStart_7496452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496455 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_7496455 : Nat := 118140960795 + 7496455 * 2 ^ 59
def prefixEnd_7496455 : Nat := 4983230072969 + 3 ^ 40 * 7496455 * 2
def baseEnd_7496455 : Nat := 3849284619800572819036937

theorem tailTrace_7496455 : CollatzResearch.WordTrace tailWord_7496455 prefixEnd_7496455 3849284619800572819036937 := by
  unfold tailWord_7496455
  simp only [CollatzResearch.WordTrace]
  refine ⟨273418176056631302429810819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182278784037754201619873879 273418176056631302429810819)
  ·
    refine ⟨410127264084946953644716229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273418176056631302429810819 410127264084946953644716229)
    ·
      refine ⟨76898862015927553808384293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410127264084946953644716229 76898862015927553808384293)
      ·
        refine ⟨14418536627986416339072055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76898862015927553808384293 14418536627986416339072055)
        ·
          refine ⟨21627804941979624508608083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418536627986416339072055 21627804941979624508608083)
          ·
            refine ⟨32441707412969436762912125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21627804941979624508608083 32441707412969436762912125)
            ·
              refine ⟨12165640279863538786092047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32441707412969436762912125 12165640279863538786092047)
              ·
                refine ⟨18248460419795308179138071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12165640279863538786092047 18248460419795308179138071)
                ·
                  refine ⟨27372690629692962268707107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18248460419795308179138071 27372690629692962268707107)
                  ·
                    refine ⟨41059035944539443403060661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27372690629692962268707107 41059035944539443403060661)
                    ·
                      refine ⟨3849284619800572819036937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41059035944539443403060661 3849284619800572819036937)
                      ·
                        rfl

theorem cell23_7496455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_7496455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496455 prefixEnd_7496455 := by exact prefixLift 7496455
  have htrace : WordTrace (prefixWord ++ tailWord_7496455) baseStart_7496455 baseEnd_7496455 := by
    simpa [prefixWord, tailWord_7496455, baseEnd_7496455] using wordTrace_append hprefix tailTrace_7496455
  have hstable : (prefixWord ++ tailWord_7496455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496455).length < 2 ^ (prefixWord ++ tailWord_7496455).sum := by decide
  have hdescent : baseEnd_7496455 < baseStart_7496455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496469 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_7496469 : Nat := 118140960795 + 7496469 * 2 ^ 59
def prefixEnd_7496469 : Nat := 4983230072969 + 3 ^ 40 * 7496469 * 2
def baseEnd_7496469 : Nat := 3849291808529735764261873

theorem tailTrace_7496469 : CollatzResearch.WordTrace tailWord_7496469 prefixEnd_7496469 3849291808529735764261873 := by
  unfold tailWord_7496469
  simp only [CollatzResearch.WordTrace]
  refine ⟨273418686678580582820820461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182279124452387055213880307 273418686678580582820820461)
  ·
    refine ⟨102532007504467718557807673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273418686678580582820820461 102532007504467718557807673)
    ·
      refine ⟨76899005628350788918355755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102532007504467718557807673 76899005628350788918355755)
      ·
        refine ⟨115348508442526183377533633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76899005628350788918355755 115348508442526183377533633)
        ·
          refine ⟨86511381331894637533150225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115348508442526183377533633 86511381331894637533150225)
          ·
            refine ⟨64883535998920978149862669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86511381331894637533150225 64883535998920978149862669)
            ·
              refine ⟨24331325999595366806198501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64883535998920978149862669 24331325999595366806198501)
              ·
                refine ⟨4562123624924131276162219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24331325999595366806198501 4562123624924131276162219)
                ·
                  refine ⟨6843185437386196914243329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562123624924131276162219 6843185437386196914243329)
                  ·
                    refine ⟨5132389078039647685682497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6843185437386196914243329 5132389078039647685682497)
                    ·
                      refine ⟨3849291808529735764261873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132389078039647685682497 3849291808529735764261873)
                      ·
                        rfl

theorem cell23_7496469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_7496469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496469 prefixEnd_7496469 := by exact prefixLift 7496469
  have htrace : WordTrace (prefixWord ++ tailWord_7496469) baseStart_7496469 baseEnd_7496469 := by
    simpa [prefixWord, tailWord_7496469, baseEnd_7496469] using wordTrace_append hprefix tailTrace_7496469
  have hstable : (prefixWord ++ tailWord_7496469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496469).length < 2 ^ (prefixWord ++ tailWord_7496469).sum := by decide
  have hdescent : baseEnd_7496469 < baseStart_7496469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496485 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_7496485 : Nat := 118140960795 + 7496485 * 2 ^ 59
def prefixEnd_7496485 : Nat := 4983230072969 + 3 ^ 40 * 7496485 * 2
def baseEnd_7496485 : Nat := 3849300024220207701661799

theorem tailTrace_7496485 : CollatzResearch.WordTrace tailWord_7496485 prefixEnd_7496485 3849300024220207701661799 := by
  unfold tailWord_7496485
  simp only [CollatzResearch.WordTrace]
  refine ⟨273419270246522617553402909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182279513497681745035601939 273419270246522617553402909)
  ·
    refine ⟨102532226342445981582526091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273419270246522617553402909 102532226342445981582526091)
    ·
      refine ⟨153798339513668972373789137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102532226342445981582526091 153798339513668972373789137)
      ·
        refine ⟨115348754635251729280341853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153798339513668972373789137 115348754635251729280341853)
        ·
          refine ⟨43255782988219398480128195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115348754635251729280341853 43255782988219398480128195)
          ·
            refine ⟨64883674482329097720192293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43255782988219398480128195 64883674482329097720192293)
            ·
              refine ⟨12165688965436705822536055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64883674482329097720192293 12165688965436705822536055)
              ·
                refine ⟨18248533448155058733804083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12165688965436705822536055 18248533448155058733804083)
                ·
                  refine ⟨27372800172232588100706125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18248533448155058733804083 27372800172232588100706125)
                  ·
                    refine ⟨10264800064587220537764797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27372800172232588100706125 10264800064587220537764797)
                    ·
                      refine ⟨3849300024220207701661799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264800064587220537764797 3849300024220207701661799)
                      ·
                        rfl

theorem cell23_7496485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_7496485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496485 prefixEnd_7496485 := by exact prefixLift 7496485
  have htrace : WordTrace (prefixWord ++ tailWord_7496485) baseStart_7496485 baseEnd_7496485 := by
    simpa [prefixWord, tailWord_7496485, baseEnd_7496485] using wordTrace_append hprefix tailTrace_7496485
  have hstable : (prefixWord ++ tailWord_7496485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496485).length < 2 ^ (prefixWord ++ tailWord_7496485).sum := by decide
  have hdescent : baseEnd_7496485 < baseStart_7496485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496488 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7496488 : Nat := 118140960795 + 7496488 * 2 ^ 59
def prefixEnd_7496488 : Nat := 4983230072969 + 3 ^ 40 * 7496488 * 2
def baseEnd_7496488 : Nat := 1283100521554057063308095

theorem tailTrace_7496488 : CollatzResearch.WordTrace tailWord_7496488 prefixEnd_7496488 1283100521554057063308095 := by
  unfold tailWord_7496488
  simp only [CollatzResearch.WordTrace]
  refine ⟨136709689832755874532881059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182279586443674499377174745 136709689832755874532881059)
  ·
    refine ⟨205064534749133811799321589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136709689832755874532881059 205064534749133811799321589)
    ·
      refine ⟨19224800132731294856186399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205064534749133811799321589 19224800132731294856186399)
      ·
        refine ⟨28837200199096942284279599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19224800132731294856186399 28837200199096942284279599)
        ·
          refine ⟨43255800298645413426419399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28837200199096942284279599 43255800298645413426419399)
          ·
            refine ⟨64883700447968120139629099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43255800298645413426419399 64883700447968120139629099)
            ·
              refine ⟨97325550671952180209443649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64883700447968120139629099 97325550671952180209443649)
              ·
                refine ⟨72994163003964135157082737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97325550671952180209443649 72994163003964135157082737)
                ·
                  refine ⟨54745622252973101367812053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72994163003964135157082737 54745622252973101367812053)
                  ·
                    refine ⟨1283100521554057063308095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54745622252973101367812053 1283100521554057063308095)
                    ·
                      rfl

theorem cell23_7496488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7496488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496488 prefixEnd_7496488 := by exact prefixLift 7496488
  have htrace : WordTrace (prefixWord ++ tailWord_7496488) baseStart_7496488 baseEnd_7496488 := by
    simpa [prefixWord, tailWord_7496488, baseEnd_7496488] using wordTrace_append hprefix tailTrace_7496488
  have hstable : (prefixWord ++ tailWord_7496488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496488).length < 2 ^ (prefixWord ++ tailWord_7496488).sum := by decide
  have hdescent : baseEnd_7496488 < baseStart_7496488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496491 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_7496491 : Nat := 118140960795 + 7496491 * 2 ^ 59
def prefixEnd_7496491 : Nat := 4983230072969 + 3 ^ 40 * 7496491 * 2
def baseEnd_7496491 : Nat := 3849303105104134678186771

theorem tailTrace_7496491 : CollatzResearch.WordTrace tailWord_7496491 prefixEnd_7496491 3849303105104134678186771 := by
  unfold tailWord_7496491
  simp only [CollatzResearch.WordTrace]
  refine ⟨273419489084500880578121327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182279659389667253718747551 273419489084500880578121327)
  ·
    refine ⟨410129233626751320867181991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273419489084500880578121327 410129233626751320867181991)
    ·
      refine ⟨615193850440126981300772987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410129233626751320867181991 615193850440126981300772987)
      ·
        refine ⟨922790775660190471951159481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615193850440126981300772987 922790775660190471951159481)
        ·
          refine ⟨692093081745142853963369611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922790775660190471951159481 692093081745142853963369611)
          ·
            refine ⟨1038139622617714280945054417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692093081745142853963369611 1038139622617714280945054417)
            ·
              refine ⟨778604716963285710708790813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038139622617714280945054417 778604716963285710708790813)
              ·
                refine ⟨291976768861232141515796555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778604716963285710708790813 291976768861232141515796555)
                ·
                  refine ⟨437965153291848212273694833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291976768861232141515796555 437965153291848212273694833)
                  ·
                    refine ⟨328473864968886159205271125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437965153291848212273694833 328473864968886159205271125)
                    ·
                      refine ⟨3849303105104134678186771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328473864968886159205271125 3849303105104134678186771)
                      ·
                        rfl

theorem cell23_7496491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_7496491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496491 prefixEnd_7496491 := by exact prefixLift 7496491
  have htrace : WordTrace (prefixWord ++ tailWord_7496491) baseStart_7496491 baseEnd_7496491 := by
    simpa [prefixWord, tailWord_7496491, baseEnd_7496491] using wordTrace_append hprefix tailTrace_7496491
  have hstable : (prefixWord ++ tailWord_7496491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496491).length < 2 ^ (prefixWord ++ tailWord_7496491).sum := by decide
  have hdescent : baseEnd_7496491 < baseStart_7496491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496498 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_7496498 : Nat := 118140960795 + 7496498 * 2 ^ 59
def prefixEnd_7496498 : Nat := 4983230072969 + 3 ^ 40 * 7496498 * 2
def baseEnd_7496498 : Nat := 3849306699468716150799239

theorem tailTrace_7496498 : CollatzResearch.WordTrace tailWord_7496498 prefixEnd_7496498 3849306699468716150799239 := by
  unfold tailWord_7496498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68354936098868880193406537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182279829596983680515750765 68354936098868880193406537)
  ·
    refine ⟨51266202074151660145054903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68354936098868880193406537 51266202074151660145054903)
    ·
      refine ⟨76899303111227490217582355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51266202074151660145054903 76899303111227490217582355)
      ·
        refine ⟨115348954666841235326373533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76899303111227490217582355 115348954666841235326373533)
        ·
          refine ⟨43255858000065463247390075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115348954666841235326373533 43255858000065463247390075)
          ·
            refine ⟨64883787000098194871085113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43255858000065463247390075 64883787000098194871085113)
            ·
              refine ⟨48662840250073646153313835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64883787000098194871085113 48662840250073646153313835)
              ·
                refine ⟨72994260375110469229970753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48662840250073646153313835 72994260375110469229970753)
                ·
                  refine ⟨54745695281332851922478065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72994260375110469229970753 54745695281332851922478065)
                  ·
                    refine ⟨41059271460999638941858549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54745695281332851922478065 41059271460999638941858549)
                    ·
                      refine ⟨3849306699468716150799239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41059271460999638941858549 3849306699468716150799239)
                      ·
                        rfl

theorem cell23_7496498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_7496498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496498 prefixEnd_7496498 := by exact prefixLift 7496498
  have htrace : WordTrace (prefixWord ++ tailWord_7496498) baseStart_7496498 baseEnd_7496498 := by
    simpa [prefixWord, tailWord_7496498, baseEnd_7496498] using wordTrace_append hprefix tailTrace_7496498
  have hstable : (prefixWord ++ tailWord_7496498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496498).length < 2 ^ (prefixWord ++ tailWord_7496498).sum := by decide
  have hdescent : baseEnd_7496498 < baseStart_7496498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496506 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_7496506 : Nat := 118140960795 + 7496506 * 2 ^ 59
def prefixEnd_7496506 : Nat := 4983230072969 + 3 ^ 40 * 7496506 * 2
def baseEnd_7496506 : Nat := 3849310807313952119499203

theorem tailTrace_7496506 : CollatzResearch.WordTrace tailWord_7496506 prefixEnd_7496506 3849310807313952119499203 := by
  unfold tailWord_7496506
  simp only [CollatzResearch.WordTrace]
  refine ⟨68355009044861634534979343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182280024119631025426611581 68355009044861634534979343)
  ·
    refine ⟨102532513567292451802469015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68355009044861634534979343 102532513567292451802469015)
    ·
      refine ⟨153798770350938677703703523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102532513567292451802469015 153798770350938677703703523)
      ·
        refine ⟨230698155526408016555555285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153798770350938677703703523 230698155526408016555555285)
        ·
          refine ⟨5406988020150187888020827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 230698155526408016555555285 5406988020150187888020827)
          ·
            refine ⟨8110482030225281832031241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406988020150187888020827 8110482030225281832031241)
            ·
              refine ⟨6082861522668961374023431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110482030225281832031241 6082861522668961374023431)
              ·
                refine ⟨9124292284003442061035147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082861522668961374023431 9124292284003442061035147)
                ·
                  refine ⟨13686438426005163091552721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124292284003442061035147 13686438426005163091552721)
                  ·
                    refine ⟨10264828819503872318664541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13686438426005163091552721 10264828819503872318664541)
                    ·
                      refine ⟨3849310807313952119499203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264828819503872318664541 3849310807313952119499203)
                      ·
                        rfl

theorem cell23_7496506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_7496506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496506 prefixEnd_7496506 := by exact prefixLift 7496506
  have htrace : WordTrace (prefixWord ++ tailWord_7496506) baseStart_7496506 baseEnd_7496506 := by
    simpa [prefixWord, tailWord_7496506, baseEnd_7496506] using wordTrace_append hprefix tailTrace_7496506
  have hstable : (prefixWord ++ tailWord_7496506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496506).length < 2 ^ (prefixWord ++ tailWord_7496506).sum := by decide
  have hdescent : baseEnd_7496506 < baseStart_7496506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496528 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_7496528 : Nat := 118140960795 + 7496528 * 2 ^ 59
def prefixEnd_7496528 : Nat := 4983230072969 + 3 ^ 40 * 7496528 * 2
def baseEnd_7496528 : Nat := 3849322103888351033424101

theorem tailTrace_7496528 : CollatzResearch.WordTrace tailWord_7496528 prefixEnd_7496528 3849322103888351033424101 := by
  unfold tailWord_7496528
  simp only [CollatzResearch.WordTrace]
  refine ⟨136710419292683417948609119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182280559056911223931478825 136710419292683417948609119)
  ·
    refine ⟨205065628939025126922913679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136710419292683417948609119 205065628939025126922913679)
    ·
      refine ⟨307598443408537690384370519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205065628939025126922913679 307598443408537690384370519)
      ·
        refine ⟨461397665112806535576555779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307598443408537690384370519 461397665112806535576555779)
        ·
          refine ⟨692096497669209803364833669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461397665112806535576555779 692096497669209803364833669)
          ·
            refine ⟨129768093312976838130906313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 692096497669209803364833669 129768093312976838130906313)
            ·
              refine ⟨97326069984732628598179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129768093312976838130906313 97326069984732628598179735)
              ·
                refine ⟨145989104977098942897269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97326069984732628598179735 145989104977098942897269603)
                ·
                  refine ⟨218983657465648414345904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145989104977098942897269603 218983657465648414345904405)
                  ·
                    refine ⟨10264858943702269422464269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218983657465648414345904405 10264858943702269422464269)
                    ·
                      refine ⟨3849322103888351033424101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10264858943702269422464269 3849322103888351033424101)
                      ·
                        rfl

theorem cell23_7496528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_7496528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496528 prefixEnd_7496528 := by exact prefixLift 7496528
  have htrace : WordTrace (prefixWord ++ tailWord_7496528) baseStart_7496528 baseEnd_7496528 := by
    simpa [prefixWord, tailWord_7496528, baseEnd_7496528] using wordTrace_append hprefix tailTrace_7496528
  have hstable : (prefixWord ++ tailWord_7496528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496528).length < 2 ^ (prefixWord ++ tailWord_7496528).sum := by decide
  have hdescent : baseEnd_7496528 < baseStart_7496528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496546 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7496546 : Nat := 118140960795 + 7496546 * 2 ^ 59
def prefixEnd_7496546 : Nat := 4983230072969 + 3 ^ 40 * 7496546 * 2
def baseEnd_7496546 : Nat := 3849331346540131962999019

theorem tailTrace_7496546 : CollatzResearch.WordTrace tailWord_7496546 prefixEnd_7496546 3849331346540131962999019 := by
  unfold tailWord_7496546
  simp only [CollatzResearch.WordTrace]
  refine ⟨68355373774825406242843373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182280996732867749980915661 68355373774825406242843373)
  ·
    refine ⟨25633265165559527341066265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68355373774825406242843373 25633265165559527341066265)
    ·
      refine ⟨19224948874169645505799699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25633265165559527341066265 19224948874169645505799699)
      ·
        refine ⟨28837423311254468258699549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19224948874169645505799699 28837423311254468258699549)
        ·
          refine ⟨10814033741720425597012331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28837423311254468258699549 10814033741720425597012331)
          ·
            refine ⟨16221050612580638395518497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814033741720425597012331 16221050612580638395518497)
            ·
              refine ⟨12165787959435478796638873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16221050612580638395518497 12165787959435478796638873)
              ·
                refine ⟨9124340969576609097479155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12165787959435478796638873 9124340969576609097479155)
                ·
                  refine ⟨13686511454364913646218733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124340969576609097479155 13686511454364913646218733)
                  ·
                    refine ⟨5132441795386842617332025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13686511454364913646218733 5132441795386842617332025)
                    ·
                      refine ⟨3849331346540131962999019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132441795386842617332025 3849331346540131962999019)
                      ·
                        rfl

theorem cell23_7496546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7496546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496546 prefixEnd_7496546 := by exact prefixLift 7496546
  have htrace : WordTrace (prefixWord ++ tailWord_7496546) baseStart_7496546 baseEnd_7496546 := by
    simpa [prefixWord, tailWord_7496546, baseEnd_7496546] using wordTrace_append hprefix tailTrace_7496546
  have hstable : (prefixWord ++ tailWord_7496546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496546).length < 2 ^ (prefixWord ++ tailWord_7496546).sum := by decide
  have hdescent : baseEnd_7496546 < baseStart_7496546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496588 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7496588 : Nat := 118140960795 + 7496588 * 2 ^ 59
def prefixEnd_7496588 : Nat := 4983230072969 + 3 ^ 40 * 7496588 * 2
def baseEnd_7496588 : Nat := 3849352912727620798673825

theorem tailTrace_7496588 : CollatzResearch.WordTrace tailWord_7496588 prefixEnd_7496588 3849352912727620798673825 := by
  unfold tailWord_7496588
  simp only [CollatzResearch.WordTrace]
  refine ⟨136711513482574733072201209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182282017976766310762934945 136711513482574733072201209)
  ·
    refine ⟨102533635111931049804150907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136711513482574733072201209 102533635111931049804150907)
    ·
      refine ⟨153800452667896574706226361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102533635111931049804150907 153800452667896574706226361)
      ·
        refine ⟨115350339500922431029669771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153800452667896574706226361 115350339500922431029669771)
        ·
          refine ⟨173025509251383646544504657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115350339500922431029669771 173025509251383646544504657)
          ·
            refine ⟨129769131938537734908378493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173025509251383646544504657 129769131938537734908378493)
            ·
              refine ⟨48663424476951650590641935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129769131938537734908378493 48663424476951650590641935)
              ·
                refine ⟨72995136715427475885962903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48663424476951650590641935 72995136715427475885962903)
                ·
                  refine ⟨109492705073141213828944355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72995136715427475885962903 109492705073141213828944355)
                  ·
                    refine ⟨164239057609711820743416533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109492705073141213828944355 164239057609711820743416533)
                    ·
                      refine ⟨3849352912727620798673825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164239057609711820743416533 3849352912727620798673825)
                      ·
                        rfl

theorem cell23_7496588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7496588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496588 prefixEnd_7496588 := by exact prefixLift 7496588
  have htrace : WordTrace (prefixWord ++ tailWord_7496588) baseStart_7496588 baseEnd_7496588 := by
    simpa [prefixWord, tailWord_7496588, baseEnd_7496588] using wordTrace_append hprefix tailTrace_7496588
  have hstable : (prefixWord ++ tailWord_7496588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496588).length < 2 ^ (prefixWord ++ tailWord_7496588).sum := by decide
  have hdescent : baseEnd_7496588 < baseStart_7496588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496608 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_7496608 : Nat := 118140960795 + 7496608 * 2 ^ 59
def prefixEnd_7496608 : Nat := 4983230072969 + 3 ^ 40 * 7496608 * 2
def baseEnd_7496608 : Nat := 1283121060780236906807911

theorem tailTrace_7496608 : CollatzResearch.WordTrace tailWord_7496608 prefixEnd_7496608 1283121060780236906807911 := by
  unfold tailWord_7496608
  simp only [CollatzResearch.WordTrace]
  refine ⟨136711878212538504780065239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182282504283384673040086985 136711878212538504780065239)
  ·
    refine ⟨205067817318807757170097859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136711878212538504780065239 205067817318807757170097859)
    ·
      refine ⟨307601725978211635755146789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205067817318807757170097859 307601725978211635755146789)
      ·
        refine ⟨57675323620914681704090023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307601725978211635755146789 57675323620914681704090023)
        ·
          refine ⟨86512985431372022556135035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57675323620914681704090023 86512985431372022556135035)
          ·
            refine ⟨129769478147058033834202553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86512985431372022556135035 129769478147058033834202553)
            ·
              refine ⟨97327108610293525375651915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129769478147058033834202553 97327108610293525375651915)
              ·
                refine ⟨145990662915440288063477873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97327108610293525375651915 145990662915440288063477873)
                ·
                  refine ⟨109492997186580216047608405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145990662915440288063477873 109492997186580216047608405)
                  ·
                    refine ⟨1283121060780236906807911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109492997186580216047608405 1283121060780236906807911)
                    ·
                      rfl

theorem cell23_7496608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_7496608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496608 prefixEnd_7496608 := by exact prefixLift 7496608
  have htrace : WordTrace (prefixWord ++ tailWord_7496608) baseStart_7496608 baseEnd_7496608 := by
    simpa [prefixWord, tailWord_7496608, baseEnd_7496608] using wordTrace_append hprefix tailTrace_7496608
  have hstable : (prefixWord ++ tailWord_7496608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496608).length < 2 ^ (prefixWord ++ tailWord_7496608).sum := by decide
  have hdescent : baseEnd_7496608 < baseStart_7496608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496655 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 6]
def baseStart_7496655 : Nat := 118140960795 + 7496655 * 2 ^ 59
def prefixEnd_7496655 : Nat := 4983230072969 + 3 ^ 40 * 7496655 * 2
def baseEnd_7496655 : Nat := 427709701770163559615113

theorem tailTrace_7496655 : CollatzResearch.WordTrace tailWord_7496655 prefixEnd_7496655 427709701770163559615113 := by
  unfold tailWord_7496655
  simp only [CollatzResearch.WordTrace]
  refine ⟨273425470655906736587091419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182283647103937824391394279 273425470655906736587091419)
  ·
    refine ⟨410138205983860104880637129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273425470655906736587091419 410138205983860104880637129)
    ·
      refine ⟨307603654487895078660477847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410138205983860104880637129 307603654487895078660477847)
      ·
        refine ⟨461405481731842617990716771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307603654487895078660477847 461405481731842617990716771)
        ·
          refine ⟨692108222597763926986075157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461405481731842617990716771 692108222597763926986075157)
          ·
            refine ⟨32442572934270184077472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 692108222597763926986075157 32442572934270184077472273)
            ·
              refine ⟨24331929700702638058104205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32442572934270184077472273 24331929700702638058104205)
              ·
                refine ⟨9124473637763489271789077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24331929700702638058104205 9124473637763489271789077)
                ·
                  refine ⟨427709701770163559615113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9124473637763489271789077 427709701770163559615113)
                  ·
                    rfl

theorem cell23_7496655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 6].length) (baseStart_7496655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496655 prefixEnd_7496655 := by exact prefixLift 7496655
  have htrace : WordTrace (prefixWord ++ tailWord_7496655) baseStart_7496655 baseEnd_7496655 := by
    simpa [prefixWord, tailWord_7496655, baseEnd_7496655] using wordTrace_append hprefix tailTrace_7496655
  have hstable : (prefixWord ++ tailWord_7496655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496655).length < 2 ^ (prefixWord ++ tailWord_7496655).sum := by decide
  have hdescent : baseEnd_7496655 < baseStart_7496655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496669 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_7496669 : Nat := 118140960795 + 7496669 * 2 ^ 59
def prefixEnd_7496669 : Nat := 4983230072969 + 3 ^ 40 * 7496669 * 2
def baseEnd_7496669 : Nat := 3849394504660634981760953

theorem tailTrace_7496669 : CollatzResearch.WordTrace tailWord_7496669 prefixEnd_7496669 3849394504660634981760953 := by
  unfold tailWord_7496669
  simp only [CollatzResearch.WordTrace]
  refine ⟨273425981277856016978101061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182283987518570677985400707 273425981277856016978101061)
  ·
    refine ⟨51267371489598003183393949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273425981277856016978101061 51267371489598003183393949)
    ·
      refine ⟨19225264308599251193772731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51267371489598003183393949 19225264308599251193772731)
      ·
        refine ⟨28837896462898876790659097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19225264308599251193772731 28837896462898876790659097)
        ·
          refine ⟨21628422347174157592994323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28837896462898876790659097 21628422347174157592994323)
          ·
            refine ⟨32442633520761236389491485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628422347174157592994323 32442633520761236389491485)
            ·
              refine ⟨12165987570285463646059307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32442633520761236389491485 12165987570285463646059307)
              ·
                refine ⟨18248981355428195469088961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12165987570285463646059307 18248981355428195469088961)
                ·
                  refine ⟨13686736016571146601816721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18248981355428195469088961 13686736016571146601816721)
                  ·
                    refine ⟨10265052012428359951362541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13686736016571146601816721 10265052012428359951362541)
                    ·
                      refine ⟨3849394504660634981760953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10265052012428359951362541 3849394504660634981760953)
                      ·
                        rfl

theorem cell23_7496669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_7496669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496669 prefixEnd_7496669 := by exact prefixLift 7496669
  have htrace : WordTrace (prefixWord ++ tailWord_7496669) baseStart_7496669 baseEnd_7496669 := by
    simpa [prefixWord, tailWord_7496669, baseEnd_7496669] using wordTrace_append hprefix tailTrace_7496669
  have hstable : (prefixWord ++ tailWord_7496669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496669).length < 2 ^ (prefixWord ++ tailWord_7496669).sum := by decide
  have hdescent : baseEnd_7496669 < baseStart_7496669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496766 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_7496766 : Nat := 118140960795 + 7496766 * 2 ^ 59
def prefixEnd_7496766 : Nat := 4983230072969 + 3 ^ 40 * 7496766 * 2
def baseEnd_7496766 : Nat := 1283148104094707034082669

theorem tailTrace_7496766 : CollatzResearch.WordTrace tailWord_7496766 prefixEnd_7496766 1283148104094707034082669 := by
  unfold tailWord_7496766
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178689894813075318047769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182286346105669735029588101 34178689894813075318047769)
  ·
    refine ⟨25634017421109806488535827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34178689894813075318047769 25634017421109806488535827)
    ·
      refine ⟨38451026131664709732803741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25634017421109806488535827 38451026131664709732803741)
      ·
        refine ⟨14419134799374266149801403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38451026131664709732803741 14419134799374266149801403)
        ·
          refine ⟨21628702199061399224702105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419134799374266149801403 21628702199061399224702105)
          ·
            refine ⟨16221526649296049418526579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21628702199061399224702105 16221526649296049418526579)
            ·
              refine ⟨24332289973944074127789869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16221526649296049418526579 24332289973944074127789869)
              ·
                refine ⟨9124608740229027797921201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24332289973944074127789869 9124608740229027797921201)
                ·
                  refine ⟨6843456555171770848440901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9124608740229027797921201 6843456555171770848440901)
                  ·
                    refine ⟨1283148104094707034082669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843456555171770848440901 1283148104094707034082669)
                    ·
                      rfl

theorem cell23_7496766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_7496766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496766 prefixEnd_7496766 := by exact prefixLift 7496766
  have htrace : WordTrace (prefixWord ++ tailWord_7496766) baseStart_7496766 baseEnd_7496766 := by
    simpa [prefixWord, tailWord_7496766, baseEnd_7496766] using wordTrace_append hprefix tailTrace_7496766
  have hstable : (prefixWord ++ tailWord_7496766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496766).length < 2 ^ (prefixWord ++ tailWord_7496766).sum := by decide
  have hdescent : baseEnd_7496766 < baseStart_7496766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496785 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7496785 : Nat := 118140960795 + 7496785 * 2 ^ 59
def prefixEnd_7496785 : Nat := 4983230072969 + 3 ^ 40 * 7496785 * 2
def baseEnd_7496785 : Nat := 3849454068416556527910419

theorem tailTrace_7496785 : CollatzResearch.WordTrace tailWord_7496785 prefixEnd_7496785 3849454068416556527910419 := by
  unfold tailWord_7496785
  simp only [CollatzResearch.WordTrace]
  refine ⟨273430212145435768789323809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182286808096957179192882539 273430212145435768789323809)
  ·
    refine ⟨205072659109076826591992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273430212145435768789323809 205072659109076826591992857)
    ·
      refine ⟨153804494331807619943994643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205072659109076826591992857 153804494331807619943994643)
      ·
        refine ⟨230706741497711429915991965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153804494331807619943994643 230706741497711429915991965)
        ·
          refine ⟨86515028061641786218496987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230706741497711429915991965 86515028061641786218496987)
          ·
            refine ⟨129772542092462679327745481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86515028061641786218496987 129772542092462679327745481)
            ·
              refine ⟨97329406569347009495809111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129772542092462679327745481 97329406569347009495809111)
              ·
                refine ⟨145994109854020514243713667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97329406569347009495809111 145994109854020514243713667)
                ·
                  refine ⟨218991164781030771365570501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145994109854020514243713667 218991164781030771365570501)
                  ·
                    refine ⟨41060843396443269631044469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218991164781030771365570501 41060843396443269631044469)
                    ·
                      refine ⟨3849454068416556527910419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41060843396443269631044469 3849454068416556527910419)
                      ·
                        rfl

theorem cell23_7496785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7496785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496785 prefixEnd_7496785 := by exact prefixLift 7496785
  have htrace : WordTrace (prefixWord ++ tailWord_7496785) baseStart_7496785 baseEnd_7496785 := by
    simpa [prefixWord, tailWord_7496785, baseEnd_7496785] using wordTrace_append hprefix tailTrace_7496785
  have hstable : (prefixWord ++ tailWord_7496785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496785).length < 2 ^ (prefixWord ++ tailWord_7496785).sum := by decide
  have hdescent : baseEnd_7496785 < baseStart_7496785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496790 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7496790 : Nat := 118140960795 + 7496790 * 2 ^ 59
def prefixEnd_7496790 : Nat := 4983230072969 + 3 ^ 40 * 7496790 * 2
def baseEnd_7496790 : Nat := 3849456635819829008347897

theorem tailTrace_7496790 : CollatzResearch.WordTrace tailWord_7496790 prefixEnd_7496790 3849456635819829008347897 := by
  unfold tailWord_7496790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089399656901103415203489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182286929673611769762170549 17089399656901103415203489)
  ·
    refine ⟨12817049742675827561402617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17089399656901103415203489 12817049742675827561402617)
    ·
      refine ⟨9612787307006870671051963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817049742675827561402617 9612787307006870671051963)
      ·
        refine ⟨14419180960510306006577945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612787307006870671051963 14419180960510306006577945)
        ·
          refine ⟨10814385720382729504933459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419180960510306006577945 10814385720382729504933459)
          ·
            refine ⟨16221578580574094257400189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814385720382729504933459 16221578580574094257400189)
            ·
              refine ⟨6083091967715285346525071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16221578580574094257400189 6083091967715285346525071)
              ·
                refine ⟨9124637951572928019787607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083091967715285346525071 9124637951572928019787607)
                ·
                  refine ⟨13686956927359392029681411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124637951572928019787607 13686956927359392029681411)
                  ·
                    refine ⟨20530435391039088044522117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13686956927359392029681411 20530435391039088044522117)
                    ·
                      refine ⟨3849456635819829008347897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20530435391039088044522117 3849456635819829008347897)
                      ·
                        rfl

theorem cell23_7496790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7496790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496790 prefixEnd_7496790 := by exact prefixLift 7496790
  have htrace : WordTrace (prefixWord ++ tailWord_7496790) baseStart_7496790 baseEnd_7496790 := by
    simpa [prefixWord, tailWord_7496790, baseEnd_7496790] using wordTrace_append hprefix tailTrace_7496790
  have hstable : (prefixWord ++ tailWord_7496790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496790).length < 2 ^ (prefixWord ++ tailWord_7496790).sum := by decide
  have hdescent : baseEnd_7496790 < baseStart_7496790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496842 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7496842 : Nat := 118140960795 + 7496842 * 2 ^ 59
def prefixEnd_7496842 : Nat := 4983230072969 + 3 ^ 40 * 7496842 * 2
def baseEnd_7496842 : Nat := 3849483336813862804897657

theorem tailTrace_7496842 : CollatzResearch.WordTrace tailWord_7496842 prefixEnd_7496842 3849483336813862804897657 := by
  unfold tailWord_7496842
  simp only [CollatzResearch.WordTrace]
  refine ⟨68358072776557316881037195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182288194070819511682765853 68358072776557316881037195)
  ·
    refine ⟨102537109164835975321555793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68358072776557316881037195 102537109164835975321555793)
    ·
      refine ⟨76902831873626981491166845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102537109164835975321555793 76902831873626981491166845)
      ·
        refine ⟨28838561952610118059187567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76902831873626981491166845 28838561952610118059187567)
        ·
          refine ⟨43257842928915177088781351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28838561952610118059187567 43257842928915177088781351)
          ·
            refine ⟨64886764393372765633172027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43257842928915177088781351 64886764393372765633172027)
            ·
              refine ⟨97330146590059148449758041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64886764393372765633172027 97330146590059148449758041)
              ·
                refine ⟨72997609942544361337318531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97330146590059148449758041 72997609942544361337318531)
                ·
                  refine ⟨109496414913816542005977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72997609942544361337318531 109496414913816542005977797)
                  ·
                    refine ⟨20530577796340601626120837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109496414913816542005977797 20530577796340601626120837)
                    ·
                      refine ⟨3849483336813862804897657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20530577796340601626120837 3849483336813862804897657)
                      ·
                        rfl

theorem cell23_7496842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7496842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496842 prefixEnd_7496842 := by exact prefixLift 7496842
  have htrace : WordTrace (prefixWord ++ tailWord_7496842) baseStart_7496842 baseEnd_7496842 := by
    simpa [prefixWord, tailWord_7496842, baseEnd_7496842] using wordTrace_append hprefix tailTrace_7496842
  have hstable : (prefixWord ++ tailWord_7496842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496842).length < 2 ^ (prefixWord ++ tailWord_7496842).sum := by decide
  have hdescent : baseEnd_7496842 < baseStart_7496842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496846 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7496846 : Nat := 118140960795 + 7496846 * 2 ^ 59
def prefixEnd_7496846 : Nat := 4983230072969 + 3 ^ 40 * 7496846 * 2
def baseEnd_7496846 : Nat := 3849485390736480789247639

theorem tailTrace_7496846 : CollatzResearch.WordTrace tailWord_7496846 prefixEnd_7496846 3849485390736480789247639 := by
  unfold tailWord_7496846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34179054624776847025911799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182288291332143184138196261 34179054624776847025911799)
  ·
    refine ⟨51268581937165270538867699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34179054624776847025911799 51268581937165270538867699)
    ·
      refine ⟨76902872905747905808301549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51268581937165270538867699 76902872905747905808301549)
      ·
        refine ⟨28838577339655464678113081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76902872905747905808301549 28838577339655464678113081)
        ·
          refine ⟨21628933004741598508584811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28838577339655464678113081 21628933004741598508584811)
          ·
            refine ⟨32443399507112397762877217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628933004741598508584811 32443399507112397762877217)
            ·
              refine ⟨24332549630334298322157913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32443399507112397762877217 24332549630334298322157913)
              ·
                refine ⟨18249412222750723741618435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24332549630334298322157913 18249412222750723741618435)
                ·
                  refine ⟨27374118334126085612427653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18249412222750723741618435 27374118334126085612427653)
                  ·
                    refine ⟨5132647187648641052330185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27374118334126085612427653 5132647187648641052330185)
                    ·
                      refine ⟨3849485390736480789247639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132647187648641052330185 3849485390736480789247639)
                      ·
                        rfl

theorem cell23_7496846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7496846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496846 prefixEnd_7496846 := by exact prefixLift 7496846
  have htrace : WordTrace (prefixWord ++ tailWord_7496846) baseStart_7496846 baseEnd_7496846 := by
    simpa [prefixWord, tailWord_7496846, baseEnd_7496846] using wordTrace_append hprefix tailTrace_7496846
  have hstable : (prefixWord ++ tailWord_7496846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496846).length < 2 ^ (prefixWord ++ tailWord_7496846).sum := by decide
  have hdescent : baseEnd_7496846 < baseStart_7496846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496850 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7496850 : Nat := 118140960795 + 7496850 * 2 ^ 59
def prefixEnd_7496850 : Nat := 4983230072969 + 3 ^ 40 * 7496850 * 2
def baseEnd_7496850 : Nat := 3849487444659098773597621

theorem tailTrace_7496850 : CollatzResearch.WordTrace tailWord_7496850 prefixEnd_7496850 3849487444659098773597621 := by
  unfold tailWord_7496850
  simp only [CollatzResearch.WordTrace]
  refine ⟨68358145722550071222610001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182288388593466856593626669 68358145722550071222610001)
  ·
    refine ⟨51268609291912553416957501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68358145722550071222610001 51268609291912553416957501)
    ·
      refine ⟨19225728484467207531359063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51268609291912553416957501 19225728484467207531359063)
      ·
        refine ⟨28838592726700811297038595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19225728484467207531359063 28838592726700811297038595)
        ·
          refine ⟨43257889090051216945557893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28838592726700811297038595 43257889090051216945557893)
          ·
            refine ⟨8110854204384603177292105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43257889090051216945557893 8110854204384603177292105)
            ·
              refine ⟨6083140653288452382969079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110854204384603177292105 6083140653288452382969079)
              ·
                refine ⟨9124710979932678574453619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083140653288452382969079 9124710979932678574453619)
                ·
                  refine ⟨13687066469899017861680429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124710979932678574453619 13687066469899017861680429)
                  ·
                    refine ⟨5132649926212131698130161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13687066469899017861680429 5132649926212131698130161)
                    ·
                      refine ⟨3849487444659098773597621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132649926212131698130161 3849487444659098773597621)
                      ·
                        rfl

theorem cell23_7496850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7496850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496850 prefixEnd_7496850 := by exact prefixLift 7496850
  have htrace : WordTrace (prefixWord ++ tailWord_7496850) baseStart_7496850 baseEnd_7496850 := by
    simpa [prefixWord, tailWord_7496850, baseEnd_7496850] using wordTrace_append hprefix tailTrace_7496850
  have hstable : (prefixWord ++ tailWord_7496850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496850).length < 2 ^ (prefixWord ++ tailWord_7496850).sum := by decide
  have hdescent : baseEnd_7496850 < baseStart_7496850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496863 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7496863 : Nat := 118140960795 + 7496863 * 2 ^ 59
def prefixEnd_7496863 : Nat := 4983230072969 + 3 ^ 40 * 7496863 * 2
def baseEnd_7496863 : Nat := 3849494119907607222735061

theorem tailTrace_7496863 : CollatzResearch.WordTrace tailWord_7496863 prefixEnd_7496863 3849494119907607222735061 := by
  unfold tailWord_7496863
  simp only [CollatzResearch.WordTrace]
  refine ⟨273433057039153188110663243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182288704692768792073775495 273433057039153188110663243)
  ·
    refine ⟨410149585558729782165994865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273433057039153188110663243 410149585558729782165994865)
    ·
      refine ⟨307612189169047336624496149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410149585558729782165994865 307612189169047336624496149)
      ·
        refine ⟨14419321367299093904273257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307612189169047336624496149 14419321367299093904273257)
        ·
          refine ⟨10814491025474320428204943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419321367299093904273257 10814491025474320428204943)
          ·
            refine ⟨16221736538211480642307415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814491025474320428204943 16221736538211480642307415)
            ·
              refine ⟨24332604807317220963461123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16221736538211480642307415 24332604807317220963461123)
              ·
                refine ⟨36498907210975831445191685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24332604807317220963461123 36498907210975831445191685)
                ·
                  refine ⟨6843545102057968395973441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36498907210975831445191685 6843545102057968395973441)
                  ·
                    refine ⟨5132658826543476296980081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6843545102057968395973441 5132658826543476296980081)
                    ·
                      refine ⟨3849494119907607222735061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132658826543476296980081 3849494119907607222735061)
                      ·
                        rfl

theorem cell23_7496863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7496863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496863 prefixEnd_7496863 := by exact prefixLift 7496863
  have htrace : WordTrace (prefixWord ++ tailWord_7496863) baseStart_7496863 baseEnd_7496863 := by
    simpa [prefixWord, tailWord_7496863, baseEnd_7496863] using wordTrace_append hprefix tailTrace_7496863
  have hstable : (prefixWord ++ tailWord_7496863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496863).length < 2 ^ (prefixWord ++ tailWord_7496863).sum := by decide
  have hdescent : baseEnd_7496863 < baseStart_7496863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496869 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 5]
def baseStart_7496869 : Nat := 118140960795 + 7496869 * 2 ^ 59
def prefixEnd_7496869 : Nat := 4983230072969 + 3 ^ 40 * 7496869 * 2
def baseEnd_7496869 : Nat := 427721911199059355473337

theorem tailTrace_7496869 : CollatzResearch.WordTrace tailWord_7496869 prefixEnd_7496869 427721911199059355473337 := by
  unfold tailWord_7496869
  simp only [CollatzResearch.WordTrace]
  refine ⟨273433275877131451135381661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182288850584754300756921107 273433275877131451135381661)
  ·
    refine ⟨102537478453924294175768123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273433275877131451135381661 102537478453924294175768123)
    ·
      refine ⟨153806217680886441263652185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102537478453924294175768123 153806217680886441263652185)
      ·
        refine ⟨115354663260664830947739139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153806217680886441263652185 115354663260664830947739139)
        ·
          refine ⟨173031994890997246421608709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115354663260664830947739139 173031994890997246421608709)
          ·
            refine ⟨32443499042061983704051633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173031994890997246421608709 32443499042061983704051633)
            ·
              refine ⟨24332624281546487778038725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32443499042061983704051633 24332624281546487778038725)
              ·
                refine ⟨4562367052789966458382261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24332624281546487778038725 4562367052789966458382261)
                ·
                  refine ⟨427721911199059355473337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4562367052789966458382261 427721911199059355473337)
                  ·
                    rfl

theorem cell23_7496869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_7496869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496869 prefixEnd_7496869 := by exact prefixLift 7496869
  have htrace : WordTrace (prefixWord ++ tailWord_7496869) baseStart_7496869 baseEnd_7496869 := by
    simpa [prefixWord, tailWord_7496869, baseEnd_7496869] using wordTrace_append hprefix tailTrace_7496869
  have hstable : (prefixWord ++ tailWord_7496869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496869).length < 2 ^ (prefixWord ++ tailWord_7496869).sum := by decide
  have hdescent : baseEnd_7496869 < baseStart_7496869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496882 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_7496882 : Nat := 118140960795 + 7496882 * 2 ^ 59
def prefixEnd_7496882 : Nat := 4983230072969 + 3 ^ 40 * 7496882 * 2
def baseEnd_7496882 : Nat := 1283167958680014216132491

theorem tailTrace_7496882 : CollatzResearch.WordTrace tailWord_7496882 prefixEnd_7496882 1283167958680014216132491 := by
  unfold tailWord_7496882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68358437506521088588901225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182289166684056236237069933 68358437506521088588901225)
  ·
    refine ⟨51268828129890816441675919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68358437506521088588901225 51268828129890816441675919)
    ·
      refine ⟨76903242194836224662513879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51268828129890816441675919 76903242194836224662513879)
      ·
        refine ⟨115354863292254336993770819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76903242194836224662513879 115354863292254336993770819)
        ·
          refine ⟨173032294938381505490656229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115354863292254336993770819 173032294938381505490656229)
          ·
            refine ⟨32443555300946532279498043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173032294938381505490656229 32443555300946532279498043)
            ·
              refine ⟨48665332951419798419247065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32443555300946532279498043 48665332951419798419247065)
              ·
                refine ⟨36498999713564848814435299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48665332951419798419247065 36498999713564848814435299)
                ·
                  refine ⟨54748499570347273221652949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36498999713564848814435299 54748499570347273221652949)
                  ·
                    refine ⟨1283167958680014216132491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54748499570347273221652949 1283167958680014216132491)
                    ·
                      rfl

theorem cell23_7496882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_7496882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496882 prefixEnd_7496882 := by exact prefixLift 7496882
  have htrace : WordTrace (prefixWord ++ tailWord_7496882) baseStart_7496882 baseEnd_7496882 := by
    simpa [prefixWord, tailWord_7496882, baseEnd_7496882] using wordTrace_append hprefix tailTrace_7496882
  have hstable : (prefixWord ++ tailWord_7496882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496882).length < 2 ^ (prefixWord ++ tailWord_7496882).sum := by decide
  have hdescent : baseEnd_7496882 < baseStart_7496882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496919 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_7496919 : Nat := 118140960795 + 7496919 * 2 ^ 59
def prefixEnd_7496919 : Nat := 4983230072969 + 3 ^ 40 * 7496919 * 2
def baseEnd_7496919 : Nat := 3849522874824259003634803

theorem tailTrace_7496919 : CollatzResearch.WordTrace tailWord_7496919 prefixEnd_7496919 3849522874824259003634803 := by
  unfold tailWord_7496919
  simp only [CollatzResearch.WordTrace]
  refine ⟨273435099526950309674701811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182290066351300206449801207 273435099526950309674701811)
  ·
    refine ⟨410152649290425464512052717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273435099526950309674701811 410152649290425464512052717)
    ·
      refine ⟨153807243483909549192019769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410152649290425464512052717 153807243483909549192019769)
      ·
        refine ⟨115355432612932161894014827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153807243483909549192019769 115355432612932161894014827)
        ·
          refine ⟨173033148919398242841022241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115355432612932161894014827 173033148919398242841022241)
          ·
            refine ⟨129774861689548682130766681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173033148919398242841022241 129774861689548682130766681)
            ·
              refine ⟨97331146267161511598075011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129774861689548682130766681 97331146267161511598075011)
              ·
                refine ⟨145996719400742267397112517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97331146267161511598075011 145996719400742267397112517)
                ·
                  refine ⟨27374384887639175136958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145996719400742267397112517 27374384887639175136958597)
                  ·
                    refine ⟨5132697166432345338179737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27374384887639175136958597 5132697166432345338179737)
                    ·
                      refine ⟨3849522874824259003634803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132697166432345338179737 3849522874824259003634803)
                      ·
                        rfl

theorem cell23_7496919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_7496919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496919 prefixEnd_7496919 := by exact prefixLift 7496919
  have htrace : WordTrace (prefixWord ++ tailWord_7496919) baseStart_7496919 baseEnd_7496919 := by
    simpa [prefixWord, tailWord_7496919, baseEnd_7496919] using wordTrace_append hprefix tailTrace_7496919
  have hstable : (prefixWord ++ tailWord_7496919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496919).length < 2 ^ (prefixWord ++ tailWord_7496919).sum := by decide
  have hdescent : baseEnd_7496919 < baseStart_7496919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496932 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_7496932 : Nat := 118140960795 + 7496932 * 2 ^ 59
def prefixEnd_7496932 : Nat := 4983230072969 + 3 ^ 40 * 7496932 * 2
def baseEnd_7496932 : Nat := 3849529550072767452772243

theorem tailTrace_7496932 : CollatzResearch.WordTrace tailWord_7496932 prefixEnd_7496932 3849529550072767452772243 := by
  unfold tailWord_7496932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136717786837951606447462525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182290382450602141929950033 136717786837951606447462525)
  ·
    refine ⟨51269170064231852417798447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136717786837951606447462525 51269170064231852417798447)
    ·
      refine ⟨76903755096347778626697671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51269170064231852417798447 76903755096347778626697671)
      ·
        refine ⟨115355632644521667940046507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76903755096347778626697671 115355632644521667940046507)
        ·
          refine ⟨173033448966782501910069761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115355632644521667940046507 173033448966782501910069761)
          ·
            refine ⟨129775086725086876432552321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173033448966782501910069761 129775086725086876432552321)
            ·
              refine ⟨97331315043815157324414241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129775086725086876432552321 97331315043815157324414241)
              ·
                refine ⟨72998486282861367993310681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97331315043815157324414241 72998486282861367993310681)
                ·
                  refine ⟨54748864712146025994983011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72998486282861367993310681 54748864712146025994983011)
                  ·
                    refine ⟨82123297068219038992474517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54748864712146025994983011 82123297068219038992474517)
                    ·
                      refine ⟨3849529550072767452772243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82123297068219038992474517 3849529550072767452772243)
                      ·
                        rfl

theorem cell23_7496932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_7496932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496932 prefixEnd_7496932 := by exact prefixLift 7496932
  have htrace : WordTrace (prefixWord ++ tailWord_7496932) baseStart_7496932 baseEnd_7496932 := by
    simpa [prefixWord, tailWord_7496932, baseEnd_7496932] using wordTrace_append hprefix tailTrace_7496932
  have hstable : (prefixWord ++ tailWord_7496932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496932).length < 2 ^ (prefixWord ++ tailWord_7496932).sum := by decide
  have hdescent : baseEnd_7496932 < baseStart_7496932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496979 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 5, 2]
def baseStart_7496979 : Nat := 118140960795 + 7496979 * 2 ^ 59
def prefixEnd_7496979 : Nat := 4983230072969 + 3 ^ 40 * 7496979 * 2
def baseEnd_7496979 : Nat := 3849553683663528768884527

theorem tailTrace_7496979 : CollatzResearch.WordTrace tailWord_7496979 prefixEnd_7496979 3849553683663528768884527 := by
  unfold tailWord_7496979
  simp only [CollatzResearch.WordTrace]
  refine ⟨273437287906732939921885991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182291525271155293281257327 273437287906732939921885991)
  ·
    refine ⟨410155931860099409882828987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273437287906732939921885991 410155931860099409882828987)
    ·
      refine ⟨615233897790149114824243481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410155931860099409882828987 615233897790149114824243481)
      ·
        refine ⟨461425423342611836118182611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615233897790149114824243481 461425423342611836118182611)
        ·
          refine ⟨692138135013917754177273917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461425423342611836118182611 692138135013917754177273917)
          ·
            refine ⟨259551800630219157816477719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692138135013917754177273917 259551800630219157816477719)
            ·
              refine ⟨389327700945328736724716579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259551800630219157816477719 389327700945328736724716579)
              ·
                refine ⟨583991551417993105087074869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389327700945328736724716579 583991551417993105087074869)
                ·
                  refine ⟨54749207945436853601913269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 583991551417993105087074869 54749207945436853601913269)
                  ·
                    refine ⟨5132738244884705025179369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54749207945436853601913269 5132738244884705025179369)
                    ·
                      refine ⟨3849553683663528768884527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132738244884705025179369 3849553683663528768884527)
                      ·
                        rfl

theorem cell23_7496979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5, 2].length) (baseStart_7496979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496979 prefixEnd_7496979 := by exact prefixLift 7496979
  have htrace : WordTrace (prefixWord ++ tailWord_7496979) baseStart_7496979 baseEnd_7496979 := by
    simpa [prefixWord, tailWord_7496979, baseEnd_7496979] using wordTrace_append hprefix tailTrace_7496979
  have hstable : (prefixWord ++ tailWord_7496979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496979).length < 2 ^ (prefixWord ++ tailWord_7496979).sum := by decide
  have hdescent : baseEnd_7496979 < baseStart_7496979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7496996 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_7496996 : Nat := 118140960795 + 7496996 * 2 ^ 59
def prefixEnd_7496996 : Nat := 4983230072969 + 3 ^ 40 * 7496996 * 2
def baseEnd_7496996 : Nat := 3849562412834655202371949

theorem tailTrace_7496996 : CollatzResearch.WordTrace tailWord_7496996 prefixEnd_7496996 3849562412834655202371949 := by
  unfold tailWord_7496996
  simp only [CollatzResearch.WordTrace]
  refine ⟨136718953973835675912627421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182291938631780901216836561 136718953973835675912627421)
  ·
    refine ⟨51269607740188378467235283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136718953973835675912627421 51269607740188378467235283)
    ·
      refine ⟨76904411610282567700852925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51269607740188378467235283 76904411610282567700852925)
      ·
        refine ⟨28839154353855962887819847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76904411610282567700852925 28839154353855962887819847)
        ·
          refine ⟨43258731530783944331729771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28839154353855962887819847 43258731530783944331729771)
          ·
            refine ⟨64888097296175916497594657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43258731530783944331729771 64888097296175916497594657)
            ·
              refine ⟨48666072972131937373195993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64888097296175916497594657 48666072972131937373195993)
              ·
                refine ⟨36499554729098953029896995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48666072972131937373195993 36499554729098953029896995)
                ·
                  refine ⟨54749332093648429544845493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36499554729098953029896995 54749332093648429544845493)
                  ·
                    refine ⟨5132749883779540269829265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54749332093648429544845493 5132749883779540269829265)
                    ·
                      refine ⟨3849562412834655202371949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132749883779540269829265 3849562412834655202371949)
                      ·
                        rfl

theorem cell23_7496996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_7496996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7496996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7496996 prefixEnd_7496996 := by exact prefixLift 7496996
  have htrace : WordTrace (prefixWord ++ tailWord_7496996) baseStart_7496996 baseEnd_7496996 := by
    simpa [prefixWord, tailWord_7496996, baseEnd_7496996] using wordTrace_append hprefix tailTrace_7496996
  have hstable : (prefixWord ++ tailWord_7496996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7496996).length < 2 ^ (prefixWord ++ tailWord_7496996).sum := by decide
  have hdescent : baseEnd_7496996 < baseStart_7496996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7496996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497013 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_7497013 : Nat := 118140960795 + 7497013 * 2 ^ 59
def prefixEnd_7497013 : Nat := 4983230072969 + 3 ^ 40 * 7497013 * 2
def baseEnd_7497013 : Nat := 3849571142005781635859371

theorem tailTrace_7497013 : CollatzResearch.WordTrace tailWord_7497013 prefixEnd_7497013 3849571142005781635859371 := by
  unfold tailWord_7497013
  simp only [CollatzResearch.WordTrace]
  refine ⟨273438527988609763728623693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182292351992406509152415795 273438527988609763728623693)
  ·
    refine ⟨102539447995728661398233885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273438527988609763728623693 102539447995728661398233885)
    ·
      refine ⟨38452292998398248024337707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102539447995728661398233885 38452292998398248024337707)
      ·
        refine ⟨57678439497597372036506561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38452292998398248024337707 57678439497597372036506561)
        ·
          refine ⟨43258829623198029027379921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57678439497597372036506561 43258829623198029027379921)
          ·
            refine ⟨32444122217398521770534941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43258829623198029027379921 32444122217398521770534941)
            ·
              refine ⟨12166545831524445663950603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32444122217398521770534941 12166545831524445663950603)
              ·
                refine ⟨18249818747286668495925905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166545831524445663950603 18249818747286668495925905)
                ·
                  refine ⟨13687364060465001371944429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18249818747286668495925905 13687364060465001371944429)
                  ·
                    refine ⟨5132761522674375514479161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13687364060465001371944429 5132761522674375514479161)
                    ·
                      refine ⟨3849571142005781635859371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132761522674375514479161 3849571142005781635859371)
                      ·
                        rfl

theorem cell23_7497013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_7497013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497013 prefixEnd_7497013 := by exact prefixLift 7497013
  have htrace : WordTrace (prefixWord ++ tailWord_7497013) baseStart_7497013 baseEnd_7497013 := by
    simpa [prefixWord, tailWord_7497013, baseEnd_7497013] using wordTrace_append hprefix tailTrace_7497013
  have hstable : (prefixWord ++ tailWord_7497013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497013).length < 2 ^ (prefixWord ++ tailWord_7497013).sum := by decide
  have hdescent : baseEnd_7497013 < baseStart_7497013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497020 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_7497020 : Nat := 118140960795 + 7497020 * 2 ^ 59
def prefixEnd_7497020 : Nat := 4983230072969 + 3 ^ 40 * 7497020 * 2
def baseEnd_7497020 : Nat := 3849574736370363108471839

theorem tailTrace_7497020 : CollatzResearch.WordTrace tailWord_7497020 prefixEnd_7497020 3849574736370363108471839 := by
  unfold tailWord_7497020
  simp only [CollatzResearch.WordTrace]
  refine ⟨136719391649792201962064257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182292522199722935949419009 136719391649792201962064257)
  ·
    refine ⟨102539543737344151471548193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136719391649792201962064257 102539543737344151471548193)
    ·
      refine ⟨76904657803008113603661145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102539543737344151471548193 76904657803008113603661145)
      ·
        refine ⟨57678493352256085202745859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76904657803008113603661145 57678493352256085202745859)
        ·
          refine ⟨86517740028384127804118789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57678493352256085202745859 86517740028384127804118789)
          ·
            refine ⟨16222076255322023963272273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86517740028384127804118789 16222076255322023963272273)
            ·
              refine ⟨12166557191491517972454205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16222076255322023963272273 12166557191491517972454205)
              ·
                refine ⟨4562458946809319239670327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12166557191491517972454205 4562458946809319239670327)
                ·
                  refine ⟨6843688420213978859505491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562458946809319239670327 6843688420213978859505491)
                  ·
                    refine ⟨10265532630320968289258237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6843688420213978859505491 10265532630320968289258237)
                    ·
                      refine ⟨3849574736370363108471839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10265532630320968289258237 3849574736370363108471839)
                      ·
                        rfl

theorem cell23_7497020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_7497020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497020 prefixEnd_7497020 := by exact prefixLift 7497020
  have htrace : WordTrace (prefixWord ++ tailWord_7497020) baseStart_7497020 baseEnd_7497020 := by
    simpa [prefixWord, tailWord_7497020, baseEnd_7497020] using wordTrace_append hprefix tailTrace_7497020
  have hstable : (prefixWord ++ tailWord_7497020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497020).length < 2 ^ (prefixWord ++ tailWord_7497020).sum := by decide
  have hdescent : baseEnd_7497020 < baseStart_7497020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497023 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 1, 5]
def baseStart_7497023 : Nat := 118140960795 + 7497023 * 2 ^ 59
def prefixEnd_7497023 : Nat := 4983230072969 + 3 ^ 40 * 7497023 * 2
def baseEnd_7497023 : Nat := 1283192092270775532244775

theorem tailTrace_7497023 : CollatzResearch.WordTrace tailWord_7497023 prefixEnd_7497023 1283192092270775532244775 := by
  unfold tailWord_7497023
  simp only [CollatzResearch.WordTrace]
  refine ⟨273438892718573535436487723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182292595145715690290991815 273438892718573535436487723)
  ·
    refine ⟨410158339077860303154731585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273438892718573535436487723 410158339077860303154731585)
    ·
      refine ⟨307618754308395227366048689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410158339077860303154731585 307618754308395227366048689)
      ·
        refine ⟨230714065731296420524536517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307618754308395227366048689 230714065731296420524536517)
        ·
          refine ⟨43258887324618078848350597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230714065731296420524536517 43258887324618078848350597)
          ·
            refine ⟨8111041373365889784065737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43258887324618078848350597 8111041373365889784065737)
            ·
              refine ⟨6083281030024417338049303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8111041373365889784065737 6083281030024417338049303)
              ·
                refine ⟨9124921545036626007073955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083281030024417338049303 9124921545036626007073955)
                ·
                  refine ⟨13687382317554939010610933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124921545036626007073955 13687382317554939010610933)
                  ·
                    refine ⟨1283192092270775532244775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13687382317554939010610933 1283192092270775532244775)
                    ·
                      rfl

theorem cell23_7497023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_7497023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497023 prefixEnd_7497023 := by exact prefixLift 7497023
  have htrace : WordTrace (prefixWord ++ tailWord_7497023) baseStart_7497023 baseEnd_7497023 := by
    simpa [prefixWord, tailWord_7497023, baseEnd_7497023] using wordTrace_append hprefix tailTrace_7497023
  have hstable : (prefixWord ++ tailWord_7497023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497023).length < 2 ^ (prefixWord ++ tailWord_7497023).sum := by decide
  have hdescent : baseEnd_7497023 < baseStart_7497023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497036 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_7497036 : Nat := 118140960795 + 7497036 * 2 ^ 59
def prefixEnd_7497036 : Nat := 4983230072969 + 3 ^ 40 * 7497036 * 2
def baseEnd_7497036 : Nat := 1283194317353611681957255

theorem tailTrace_7497036 : CollatzResearch.WordTrace tailWord_7497036 prefixEnd_7497036 1283194317353611681957255 := by
  unfold tailWord_7497036
  simp only [CollatzResearch.WordTrace]
  refine ⟨136719683433763219328355481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182292911245017625771140641 136719683433763219328355481)
  ·
    refine ⟨102539762575322414496266611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136719683433763219328355481 102539762575322414496266611)
    ·
      refine ⟨153809643862983621744399917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102539762575322414496266611 153809643862983621744399917)
      ·
        refine ⟨57678616448618858154149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153809643862983621744399917 57678616448618858154149969)
        ·
          refine ⟨43258962336464143615612477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57678616448618858154149969 43258962336464143615612477)
          ·
            refine ⟨16222110876174053855854679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43258962336464143615612477 16222110876174053855854679)
            ·
              refine ⟨24333166314261080783782019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16222110876174053855854679 24333166314261080783782019)
              ·
                refine ⟨36499749471391621175673029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24333166314261080783782019 36499749471391621175673029)
                ·
                  refine ⟨6843703025885928970438693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36499749471391621175673029 6843703025885928970438693)
                  ·
                    refine ⟨1283194317353611681957255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843703025885928970438693 1283194317353611681957255)
                    ·
                      rfl

theorem cell23_7497036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_7497036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497036 prefixEnd_7497036 := by exact prefixLift 7497036
  have htrace : WordTrace (prefixWord ++ tailWord_7497036) baseStart_7497036 baseEnd_7497036 := by
    simpa [prefixWord, tailWord_7497036, baseEnd_7497036] using wordTrace_append hprefix tailTrace_7497036
  have hstable : (prefixWord ++ tailWord_7497036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497036).length < 2 ^ (prefixWord ++ tailWord_7497036).sum := by decide
  have hdescent : baseEnd_7497036 < baseStart_7497036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497037 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7497037 : Nat := 118140960795 + 7497037 * 2 ^ 59
def prefixEnd_7497037 : Nat := 4983230072969 + 3 ^ 40 * 7497037 * 2
def baseEnd_7497037 : Nat := 3849583465541489541959261

theorem tailTrace_7497037 : CollatzResearch.WordTrace tailWord_7497037 prefixEnd_7497037 3849583465541489541959261 := by
  unfold tailWord_7497037
  simp only [CollatzResearch.WordTrace]
  refine ⟨273439403340522815827497365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182292935560348543884998243 273439403340522815827497365)
  ·
    refine ⟨12817472031587006991913939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273439403340522815827497365 12817472031587006991913939)
    ·
      refine ⟨19226208047380510487870909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12817472031587006991913939 19226208047380510487870909)
      ·
        refine ⟨7209828017767691432951591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19226208047380510487870909 7209828017767691432951591)
        ·
          refine ⟨10814742026651537149427387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209828017767691432951591 10814742026651537149427387)
          ·
            refine ⟨16222113039977305724141081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814742026651537149427387 16222113039977305724141081)
            ·
              refine ⟨12166584779982979293105811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16222113039977305724141081 12166584779982979293105811)
              ·
                refine ⟨18249877169974468939658717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166584779982979293105811 18249877169974468939658717)
                ·
                  refine ⟨6843703938740425852372019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18249877169974468939658717 6843703938740425852372019)
                  ·
                    refine ⟨10265555908110638778558029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6843703938740425852372019 10265555908110638778558029)
                    ·
                      refine ⟨3849583465541489541959261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10265555908110638778558029 3849583465541489541959261)
                      ·
                        rfl

theorem cell23_7497037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7497037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497037 prefixEnd_7497037 := by exact prefixLift 7497037
  have htrace : WordTrace (prefixWord ++ tailWord_7497037) baseStart_7497037 baseEnd_7497037 := by
    simpa [prefixWord, tailWord_7497037, baseEnd_7497037] using wordTrace_append hprefix tailTrace_7497037
  have hstable : (prefixWord ++ tailWord_7497037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497037).length < 2 ^ (prefixWord ++ tailWord_7497037).sum := by decide
  have hdescent : baseEnd_7497037 < baseStart_7497037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497043 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 3, 2, 2]
def baseStart_7497043 : Nat := 118140960795 + 7497043 * 2 ^ 59
def prefixEnd_7497043 : Nat := 4983230072969 + 3 ^ 40 * 7497043 * 2
def baseEnd_7497043 : Nat := 3849586546425416518484233

theorem tailTrace_7497043 : CollatzResearch.WordTrace tailWord_7497043 prefixEnd_7497043 3849586546425416518484233 := by
  unfold tailWord_7497043
  simp only [CollatzResearch.WordTrace]
  refine ⟨273439622178501078852215783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182293081452334052568143855 273439622178501078852215783)
  ·
    refine ⟨410159433267751618278323675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273439622178501078852215783 410159433267751618278323675)
    ·
      refine ⟨615239149901627427417485513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410159433267751618278323675 615239149901627427417485513)
      ·
        refine ⟨461429362426220570563114135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615239149901627427417485513 461429362426220570563114135)
        ·
          refine ⟨692144043639330855844671203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461429362426220570563114135 692144043639330855844671203)
          ·
            refine ⟨1038216065458996283767006805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692144043639330855844671203 1038216065458996283767006805)
            ·
              refine ⟨12166594517097612700394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1038216065458996283767006805 12166594517097612700394611)
              ·
                refine ⟨18249891775646419050591917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166594517097612700394611 18249891775646419050591917)
                ·
                  refine ⟨6843709415867407143971969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18249891775646419050591917 6843709415867407143971969)
                  ·
                    refine ⟨5132782061900555357978977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6843709415867407143971969 5132782061900555357978977)
                    ·
                      refine ⟨3849586546425416518484233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5132782061900555357978977 3849586546425416518484233)
                      ·
                        rfl

theorem cell23_7497043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2, 2].length) (baseStart_7497043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497043 prefixEnd_7497043 := by exact prefixLift 7497043
  have htrace : WordTrace (prefixWord ++ tailWord_7497043) baseStart_7497043 baseEnd_7497043 := by
    simpa [prefixWord, tailWord_7497043, baseEnd_7497043] using wordTrace_append hprefix tailTrace_7497043
  have hstable : (prefixWord ++ tailWord_7497043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497043).length < 2 ^ (prefixWord ++ tailWord_7497043).sum := by decide
  have hdescent : baseEnd_7497043 < baseStart_7497043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497056 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_7497056 : Nat := 118140960795 + 7497056 * 2 ^ 59
def prefixEnd_7497056 : Nat := 4983230072969 + 3 ^ 40 * 7497056 * 2
def baseEnd_7497056 : Nat := 3849593221673924967621673

theorem tailTrace_7497056 : CollatzResearch.WordTrace tailWord_7497056 prefixEnd_7497056 3849593221673924967621673 := by
  unfold tailWord_7497056
  simp only [CollatzResearch.WordTrace]
  refine ⟨136720048163726991036219511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182293397551635988048292681 136720048163726991036219511)
  ·
    refine ⟨205080072245590486554329267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136720048163726991036219511 205080072245590486554329267)
    ·
      refine ⟨307620108368385729831493901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205080072245590486554329267 307620108368385729831493901)
      ·
        refine ⟨115357540638144648686810213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307620108368385729831493901 115357540638144648686810213)
        ·
          refine ⟨21629538869652121628776915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115357540638144648686810213 21629538869652121628776915)
          ·
            refine ⟨32444308304478182443165373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629538869652121628776915 32444308304478182443165373)
            ·
              refine ⟨12166615614179318416187015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32444308304478182443165373 12166615614179318416187015)
              ·
                refine ⟨18249923421268977624280523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12166615614179318416187015 18249923421268977624280523)
                ·
                  refine ⟨27374885131903466436420785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18249923421268977624280523 27374885131903466436420785)
                  ·
                    refine ⟨20531163848927599827315589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27374885131903466436420785 20531163848927599827315589)
                    ·
                      refine ⟨3849593221673924967621673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20531163848927599827315589 3849593221673924967621673)
                      ·
                        rfl

theorem cell23_7497056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_7497056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497056 prefixEnd_7497056 := by exact prefixLift 7497056
  have htrace : WordTrace (prefixWord ++ tailWord_7497056) baseStart_7497056 baseEnd_7497056 := by
    simpa [prefixWord, tailWord_7497056, baseEnd_7497056] using wordTrace_append hprefix tailTrace_7497056
  have hstable : (prefixWord ++ tailWord_7497056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497056).length < 2 ^ (prefixWord ++ tailWord_7497056).sum := by decide
  have hdescent : baseEnd_7497056 < baseStart_7497056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497066 : List Nat := [3, 1, 3, 3, 2, 1, 1, 9]
def baseStart_7497066 : Nat := 118140960795 + 7497066 * 2 ^ 59
def prefixEnd_7497066 : Nat := 4983230072969 + 3 ^ 40 * 7497066 * 2
def baseEnd_7497066 : Nat := 142577716906684071425801

theorem tailTrace_7497066 : CollatzResearch.WordTrace tailWord_7497066 prefixEnd_7497066 142577716906684071425801 := by
  unfold tailWord_7497066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68360115264354438445075763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182293640704945169186868701 68360115264354438445075763)
  ·
    refine ⟨102540172896531657667613645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68360115264354438445075763 102540172896531657667613645)
    ·
      refine ⟨38452564836199371625355117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102540172896531657667613645 38452564836199371625355117)
      ·
        refine ⟨14419711813574764359508169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38452564836199371625355117 14419711813574764359508169)
        ·
          refine ⟨10814783860181073269631127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419711813574764359508169 10814783860181073269631127)
          ·
            refine ⟨16222175790271609904446691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814783860181073269631127 16222175790271609904446691)
            ·
              refine ⟨24333263685407414856670037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16222175790271609904446691 24333263685407414856670037)
              ·
                refine ⟨142577716906684071425801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24333263685407414856670037 142577716906684071425801)
                ·
                  rfl

theorem cell23_7497066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_7497066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497066 prefixEnd_7497066 := by exact prefixLift 7497066
  have htrace : WordTrace (prefixWord ++ tailWord_7497066) baseStart_7497066 baseEnd_7497066 := by
    simpa [prefixWord, tailWord_7497066, baseEnd_7497066] using wordTrace_append hprefix tailTrace_7497066
  have hstable : (prefixWord ++ tailWord_7497066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497066).length < 2 ^ (prefixWord ++ tailWord_7497066).sum := by decide
  have hdescent : baseEnd_7497066 < baseStart_7497066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497099 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_7497099 : Nat := 118140960795 + 7497099 * 2 ^ 59
def prefixEnd_7497099 : Nat := 4983230072969 + 3 ^ 40 * 7497099 * 2
def baseEnd_7497099 : Nat := 3849615301342068299383975

theorem tailTrace_7497099 : CollatzResearch.WordTrace tailWord_7497099 prefixEnd_7497099 3849615301342068299383975 := by
  unfold tailWord_7497099
  simp only [CollatzResearch.WordTrace]
  refine ⟨273441664666298200416254351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182294443110865466944169567 273441664666298200416254351)
  ·
    refine ⟨410162496999447300624381527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273441664666298200416254351 410162496999447300624381527)
    ·
      refine ⟨615243745499170950936572291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410162496999447300624381527 615243745499170950936572291)
      ·
        refine ⟨922865618248756426404858437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615243745499170950936572291 922865618248756426404858437)
        ·
          refine ⟨173037303421641829950910957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 922865618248756426404858437 173037303421641829950910957)
          ·
            refine ⟨64888988783115686231591609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173037303421641829950910957 64888988783115686231591609)
            ·
              refine ⟨48666741587336764673693707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64888988783115686231591609 48666741587336764673693707)
              ·
                refine ⟨73000112381005147010540561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48666741587336764673693707 73000112381005147010540561)
                ·
                  refine ⟨54750084285753860257905421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73000112381005147010540561 54750084285753860257905421)
                  ·
                    refine ⟨20531281607157697596714533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54750084285753860257905421 20531281607157697596714533)
                    ·
                      refine ⟨3849615301342068299383975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20531281607157697596714533 3849615301342068299383975)
                      ·
                        rfl

theorem cell23_7497099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_7497099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497099 prefixEnd_7497099 := by exact prefixLift 7497099
  have htrace : WordTrace (prefixWord ++ tailWord_7497099) baseStart_7497099 baseEnd_7497099 := by
    simpa [prefixWord, tailWord_7497099, baseEnd_7497099] using wordTrace_append hprefix tailTrace_7497099
  have hstable : (prefixWord ++ tailWord_7497099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497099).length < 2 ^ (prefixWord ++ tailWord_7497099).sum := by decide
  have hdescent : baseEnd_7497099 < baseStart_7497099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497109 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7497109 : Nat := 118140960795 + 7497109 * 2 ^ 59
def prefixEnd_7497109 : Nat := 4983230072969 + 3 ^ 40 * 7497109 * 2
def baseEnd_7497109 : Nat := 1283206812049537753419643

theorem tailTrace_7497109 : CollatzResearch.WordTrace tailWord_7497109 prefixEnd_7497109 1283206812049537753419643 := by
  unfold tailWord_7497109
  simp only [CollatzResearch.WordTrace]
  refine ⟨273442029396261972124118381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182294686264174648082745587 273442029396261972124118381)
  ·
    refine ⟨102540761023598239546544393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273442029396261972124118381 102540761023598239546544393)
    ·
      refine ⟨76905570767698679659908295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102540761023598239546544393 76905570767698679659908295)
      ·
        refine ⟨115358356151548019489862443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76905570767698679659908295 115358356151548019489862443)
        ·
          refine ⟨173037534227322029234793665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115358356151548019489862443 173037534227322029234793665)
          ·
            refine ⟨129778150670491521926095249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173037534227322029234793665 129778150670491521926095249)
            ·
              refine ⟨97333613002868641444571437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129778150670491521926095249 97333613002868641444571437)
              ·
                refine ⟨36500104876075740541714289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97333613002868641444571437 36500104876075740541714289)
                ·
                  refine ⟨27375078657056805406285717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36500104876075740541714289 27375078657056805406285717)
                  ·
                    refine ⟨1283206812049537753419643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27375078657056805406285717 1283206812049537753419643)
                    ·
                      rfl

theorem cell23_7497109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7497109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497109 prefixEnd_7497109 := by exact prefixLift 7497109
  have htrace : WordTrace (prefixWord ++ tailWord_7497109) baseStart_7497109 baseEnd_7497109 := by
    simpa [prefixWord, tailWord_7497109, baseEnd_7497109] using wordTrace_append hprefix tailTrace_7497109
  have hstable : (prefixWord ++ tailWord_7497109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497109).length < 2 ^ (prefixWord ++ tailWord_7497109).sum := by decide
  have hdescent : baseEnd_7497109 < baseStart_7497109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497129 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_7497129 : Nat := 118140960795 + 7497129 * 2 ^ 59
def prefixEnd_7497129 : Nat := 4983230072969 + 3 ^ 40 * 7497129 * 2
def baseEnd_7497129 : Nat := 3849630705761703182008837

theorem tailTrace_7497129 : CollatzResearch.WordTrace tailWord_7497129 prefixEnd_7497129 3849630705761703182008837 := by
  unfold tailWord_7497129
  simp only [CollatzResearch.WordTrace]
  refine ⟨273442758856189515539846441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182295172570793010359897627 273442758856189515539846441)
  ·
    refine ⟨205082069142142136654884831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273442758856189515539846441 205082069142142136654884831)
    ·
      refine ⟨307623103713213204982327247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205082069142142136654884831 307623103713213204982327247)
      ·
        refine ⟨461434655569819807473490871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307623103713213204982327247 461434655569819807473490871)
        ·
          refine ⟨692151983354729711210236307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461434655569819807473490871 692151983354729711210236307)
          ·
            refine ⟨1038227975032094566815354461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692151983354729711210236307 1038227975032094566815354461)
            ·
              refine ⟨389335490637035462555757923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038227975032094566815354461 389335490637035462555757923)
              ·
                refine ⟨584003235955553193833636885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389335490637035462555757923 584003235955553193833636885)
                ·
                  refine ⟨27375151685416555960951729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 584003235955553193833636885 27375151685416555960951729)
                  ·
                    refine ⟨20531363764062416970713797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27375151685416555960951729 20531363764062416970713797)
                    ·
                      refine ⟨3849630705761703182008837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20531363764062416970713797 3849630705761703182008837)
                      ·
                        rfl

theorem cell23_7497129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_7497129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497129 prefixEnd_7497129 := by exact prefixLift 7497129
  have htrace : WordTrace (prefixWord ++ tailWord_7497129) baseStart_7497129 baseEnd_7497129 := by
    simpa [prefixWord, tailWord_7497129, baseEnd_7497129] using wordTrace_append hprefix tailTrace_7497129
  have hstable : (prefixWord ++ tailWord_7497129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497129).length < 2 ^ (prefixWord ++ tailWord_7497129).sum := by decide
  have hdescent : baseEnd_7497129 < baseStart_7497129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497166 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_7497166 : Nat := 118140960795 + 7497166 * 2 ^ 59
def prefixEnd_7497166 : Nat := 4983230072969 + 3 ^ 40 * 7497166 * 2
def baseEnd_7497166 : Nat := 3849649704545919537246167

theorem tailTrace_7497166 : CollatzResearch.WordTrace tailWord_7497166 prefixEnd_7497166 3849649704545919537246167 := by
  unfold tailWord_7497166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34180513544631933857367919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182296072238036980572628901 34180513544631933857367919)
  ·
    refine ⟨51270770316947900786051879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34180513544631933857367919 51270770316947900786051879)
    ·
      refine ⟨76906155475421851179077819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51270770316947900786051879 76906155475421851179077819)
      ·
        refine ⟨115359233213132776768616729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76906155475421851179077819 115359233213132776768616729)
        ·
          refine ⟨86519424909849582576462547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115359233213132776768616729 86519424909849582576462547)
          ·
            refine ⟨129779137364774373864693821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86519424909849582576462547 129779137364774373864693821)
            ·
              refine ⟨48667176511790390199260183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129779137364774373864693821 48667176511790390199260183)
              ·
                refine ⟨73000764767685585298890275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48667176511790390199260183 73000764767685585298890275)
                ·
                  refine ⟨109501147151528377948335413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73000764767685585298890275 109501147151528377948335413)
                  ·
                    refine ⟨10265732545455785432656445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109501147151528377948335413 10265732545455785432656445)
                    ·
                      refine ⟨3849649704545919537246167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10265732545455785432656445 3849649704545919537246167)
                      ·
                        rfl

theorem cell23_7497166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_7497166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497166 prefixEnd_7497166 := by exact prefixLift 7497166
  have htrace : WordTrace (prefixWord ++ tailWord_7497166) baseStart_7497166 baseEnd_7497166 := by
    simpa [prefixWord, tailWord_7497166, baseEnd_7497166] using wordTrace_append hprefix tailTrace_7497166
  have hstable : (prefixWord ++ tailWord_7497166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497166).length < 2 ^ (prefixWord ++ tailWord_7497166).sum := by decide
  have hdescent : baseEnd_7497166 < baseStart_7497166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497267 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 1, 4]
def baseStart_7497267 : Nat := 118140960795 + 7497267 * 2 ^ 59
def prefixEnd_7497267 : Nat := 4983230072969 + 3 ^ 40 * 7497267 * 2
def baseEnd_7497267 : Nat := 1283233855364007880694401

theorem tailTrace_7497267 : CollatzResearch.WordTrace tailWord_7497267 prefixEnd_7497267 1283233855364007880694401 := by
  unfold tailWord_7497267
  simp only [CollatzResearch.WordTrace]
  refine ⟨273447792129689565108370055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182298528086459710072246703 273447792129689565108370055)
  ·
    refine ⟨410171688194534347662555083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273447792129689565108370055 410171688194534347662555083)
    ·
      refine ⟨615257532291801521493832625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410171688194534347662555083 615257532291801521493832625)
      ·
        refine ⟨461443149218851141120374469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615257532291801521493832625 461443149218851141120374469)
        ·
          refine ⟨86520590478534588960070213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461443149218851141120374469 86520590478534588960070213)
          ·
            refine ⟨16222610714725235430013165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86520590478534588960070213 16222610714725235430013165)
            ·
              refine ⟨6083479018021963286254937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16222610714725235430013165 6083479018021963286254937)
              ·
                refine ⟨4562609263516472464691203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6083479018021963286254937 4562609263516472464691203)
                ·
                  refine ⟨6843913895274708697036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562609263516472464691203 6843913895274708697036805)
                  ·
                    refine ⟨1283233855364007880694401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6843913895274708697036805 1283233855364007880694401)
                    ·
                      rfl

theorem cell23_7497267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 4].length) (baseStart_7497267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497267 prefixEnd_7497267 := by exact prefixLift 7497267
  have htrace : WordTrace (prefixWord ++ tailWord_7497267) baseStart_7497267 baseEnd_7497267 := by
    simpa [prefixWord, tailWord_7497267, baseEnd_7497267] using wordTrace_append hprefix tailTrace_7497267
  have hstable : (prefixWord ++ tailWord_7497267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497267).length < 2 ^ (prefixWord ++ tailWord_7497267).sum := by decide
  have hdescent : baseEnd_7497267 < baseStart_7497267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497367 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_7497367 : Nat := 118140960795 + 7497367 * 2 ^ 59
def prefixEnd_7497367 : Nat := 4983230072969 + 3 ^ 40 * 7497367 * 2
def baseEnd_7497367 : Nat := 3849752914157473250832743

theorem tailTrace_7497367 : CollatzResearch.WordTrace tailWord_7497367 prefixEnd_7497367 3849752914157473250832743 := by
  unfold tailWord_7497367
  simp only [CollatzResearch.WordTrace]
  refine ⟨273451439429327282187010355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182300959619551521458006903 273451439429327282187010355)
  ·
    refine ⟨410177159143990923280515533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273451439429327282187010355 410177159143990923280515533)
    ·
      refine ⟨153816434678996596230193325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410177159143990923280515533 153816434678996596230193325)
      ·
        refine ⟨57681163004623723586322497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153816434678996596230193325 57681163004623723586322497)
        ·
          refine ⟨43260872253467792689741873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57681163004623723586322497 43260872253467792689741873)
          ·
            refine ⟨32445654190100844517306405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43260872253467792689741873 32445654190100844517306405)
            ·
              refine ⟨6083560160643908346994951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32445654190100844517306405 6083560160643908346994951)
              ·
                refine ⟨9125340240965862520492427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083560160643908346994951 9125340240965862520492427)
                ·
                  refine ⟨13688010361448793780738641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125340240965862520492427 13688010361448793780738641)
                  ·
                    refine ⟨10266007771086595335553981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13688010361448793780738641 10266007771086595335553981)
                    ·
                      refine ⟨3849752914157473250832743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10266007771086595335553981 3849752914157473250832743)
                      ·
                        rfl

theorem cell23_7497367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_7497367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497367 prefixEnd_7497367 := by exact prefixLift 7497367
  have htrace : WordTrace (prefixWord ++ tailWord_7497367) baseStart_7497367 baseEnd_7497367 := by
    simpa [prefixWord, tailWord_7497367, baseEnd_7497367] using wordTrace_append hprefix tailTrace_7497367
  have hstable : (prefixWord ++ tailWord_7497367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497367).length < 2 ^ (prefixWord ++ tailWord_7497367).sum := by decide
  have hdescent : baseEnd_7497367 < baseStart_7497367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497374 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7497374 : Nat := 118140960795 + 7497374 * 2 ^ 59
def prefixEnd_7497374 : Nat := 4983230072969 + 3 ^ 40 * 7497374 * 2
def baseEnd_7497374 : Nat := 1283252169507351574481737

theorem tailTrace_7497374 : CollatzResearch.WordTrace tailWord_7497374 prefixEnd_7497374 1283252169507351574481737 := by
  unfold tailWord_7497374
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181461842537740297814397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182301129826867948255010117 34181461842537740297814397)
  ·
    refine ⟨12818048190951652611680399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34181461842537740297814397 12818048190951652611680399)
    ·
      refine ⟨19227072286427478917520599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12818048190951652611680399 19227072286427478917520599)
      ·
        refine ⟨28840608429641218376280899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19227072286427478917520599 28840608429641218376280899)
        ·
          refine ⟨43260912644461827564421349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28840608429641218376280899 43260912644461827564421349)
          ·
            refine ⟨8111421120836592668329003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43260912644461827564421349 8111421120836592668329003)
            ·
              refine ⟨12167131681254889002493505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111421120836592668329003 12167131681254889002493505)
              ·
                refine ⟨9125348760941166751870129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12167131681254889002493505 9125348760941166751870129)
                ·
                  refine ⟨6844011570705875063902597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9125348760941166751870129 6844011570705875063902597)
                  ·
                    refine ⟨1283252169507351574481737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844011570705875063902597 1283252169507351574481737)
                    ·
                      rfl

theorem cell23_7497374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7497374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497374 prefixEnd_7497374 := by exact prefixLift 7497374
  have htrace : WordTrace (prefixWord ++ tailWord_7497374) baseStart_7497374 baseEnd_7497374 := by
    simpa [prefixWord, tailWord_7497374, baseEnd_7497374] using wordTrace_append hprefix tailTrace_7497374
  have hstable : (prefixWord ++ tailWord_7497374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497374).length < 2 ^ (prefixWord ++ tailWord_7497374).sum := by decide
  have hdescent : baseEnd_7497374 < baseStart_7497374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497384 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7497384 : Nat := 118140960795 + 7497384 * 2 ^ 59
def prefixEnd_7497384 : Nat := 4983230072969 + 3 ^ 40 * 7497384 * 2
def baseEnd_7497384 : Nat := 3849761643328599684320165

theorem tailTrace_7497384 : CollatzResearch.WordTrace tailWord_7497384 prefixEnd_7497384 3849761643328599684320165 := by
  unfold tailWord_7497384
  simp only [CollatzResearch.WordTrace]
  refine ⟨136726029735132847045189603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182301372980177129393586137 136726029735132847045189603)
  ·
    refine ⟨205089044602699270567784405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136726029735132847045189603 205089044602699270567784405)
    ·
      refine ⟨4806774482875764153932447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 205089044602699270567784405 4806774482875764153932447)
      ·
        refine ⟨7210161724313646230898671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4806774482875764153932447 7210161724313646230898671)
        ·
          refine ⟨10815242586470469346348007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210161724313646230898671 10815242586470469346348007)
          ·
            refine ⟨16222863879705704019522011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10815242586470469346348007 16222863879705704019522011)
            ·
              refine ⟨24334295819558556029283017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16222863879705704019522011 24334295819558556029283017)
              ·
                refine ⟨18250721864668917021962263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24334295819558556029283017 18250721864668917021962263)
                ·
                  refine ⟨27376082797003375532943395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18250721864668917021962263 27376082797003375532943395)
                  ·
                    refine ⟨41064124195505063299415093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27376082797003375532943395 41064124195505063299415093)
                    ·
                      refine ⟨3849761643328599684320165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41064124195505063299415093 3849761643328599684320165)
                      ·
                        rfl

theorem cell23_7497384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7497384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497384 prefixEnd_7497384 := by exact prefixLift 7497384
  have htrace : WordTrace (prefixWord ++ tailWord_7497384) baseStart_7497384 baseEnd_7497384 := by
    simpa [prefixWord, tailWord_7497384, baseEnd_7497384] using wordTrace_append hprefix tailTrace_7497384
  have hstable : (prefixWord ++ tailWord_7497384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497384).length < 2 ^ (prefixWord ++ tailWord_7497384).sum := by decide
  have hdescent : baseEnd_7497384 < baseStart_7497384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497407 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 1, 3, 2]
def baseStart_7497407 : Nat := 118140960795 + 7497407 * 2 ^ 59
def prefixEnd_7497407 : Nat := 4983230072969 + 3 ^ 40 * 7497407 * 2
def baseEnd_7497407 : Nat := 3849773453383653094332559

theorem tailTrace_7497407 : CollatzResearch.WordTrace tailWord_7497407 prefixEnd_7497407 3849773453383653094332559 := by
  unfold tailWord_7497407
  simp only [CollatzResearch.WordTrace]
  refine ⟨273452898349182369018466475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182301932232788246012310983 273452898349182369018466475)
  ·
    refine ⟨410179347523773553527699713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273452898349182369018466475 410179347523773553527699713)
    ·
      refine ⟨307634510642830165145774785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410179347523773553527699713 307634510642830165145774785)
      ·
        refine ⟨230725882982122623859331089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307634510642830165145774785 230725882982122623859331089)
        ·
          refine ⟨173044412236591967894498317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230725882982122623859331089 173044412236591967894498317)
          ·
            refine ⟨64891654588721987960436869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173044412236591967894498317 64891654588721987960436869)
            ·
              refine ⟨12167185235385372742581913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64891654588721987960436869 12167185235385372742581913)
              ·
                refine ⟨9125388926539029556936435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12167185235385372742581913 9125388926539029556936435)
                ·
                  refine ⟨13688083389808544335404653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125388926539029556936435 13688083389808544335404653)
                  ·
                    refine ⟨5133031271178204125776745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13688083389808544335404653 5133031271178204125776745)
                    ·
                      refine ⟨3849773453383653094332559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133031271178204125776745 3849773453383653094332559)
                      ·
                        rfl

theorem cell23_7497407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_7497407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497407 prefixEnd_7497407 := by exact prefixLift 7497407
  have htrace : WordTrace (prefixWord ++ tailWord_7497407) baseStart_7497407 baseEnd_7497407 := by
    simpa [prefixWord, tailWord_7497407, baseEnd_7497407] using wordTrace_append hprefix tailTrace_7497407
  have hstable : (prefixWord ++ tailWord_7497407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497407).length < 2 ^ (prefixWord ++ tailWord_7497407).sum := by decide
  have hdescent : baseEnd_7497407 < baseStart_7497407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497454 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_7497454 : Nat := 118140960795 + 7497454 * 2 ^ 59
def prefixEnd_7497454 : Nat := 4983230072969 + 3 ^ 40 * 7497454 * 2
def baseEnd_7497454 : Nat := 3849797586974414410444843

theorem tailTrace_7497454 : CollatzResearch.WordTrace tailWord_7497454 prefixEnd_7497454 3849797586974414410444843 := by
  unfold tailWord_7497454
  simp only [CollatzResearch.WordTrace]
  refine ⟨34181826572501512005678427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182303075053341397363618277 34181826572501512005678427)
  ·
    refine ⟨51272739858752268008517641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34181826572501512005678427 51272739858752268008517641)
    ·
      refine ⟨38454554894064201006388231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51272739858752268008517641 38454554894064201006388231)
      ·
        refine ⟨57681832341096301509582347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38454554894064201006388231 57681832341096301509582347)
        ·
          refine ⟨86522748511644452264373521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57681832341096301509582347 86522748511644452264373521)
          ·
            refine ⟨64892061383733339198280141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86522748511644452264373521 64892061383733339198280141)
            ·
              refine ⟨24334523018900002199355053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64892061383733339198280141 24334523018900002199355053)
              ·
                refine ⟨9125446132087500824758145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24334523018900002199355053 9125446132087500824758145)
                ·
                  refine ⟨6844084599065625618568609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9125446132087500824758145 6844084599065625618568609)
                  ·
                    refine ⟨5133063449299219213926457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844084599065625618568609 5133063449299219213926457)
                    ·
                      refine ⟨3849797586974414410444843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133063449299219213926457 3849797586974414410444843)
                      ·
                        rfl

theorem cell23_7497454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_7497454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497454 prefixEnd_7497454 := by exact prefixLift 7497454
  have htrace : WordTrace (prefixWord ++ tailWord_7497454) baseStart_7497454 baseEnd_7497454 := by
    simpa [prefixWord, tailWord_7497454, baseEnd_7497454] using wordTrace_append hprefix tailTrace_7497454
  have hstable : (prefixWord ++ tailWord_7497454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497454).length < 2 ^ (prefixWord ++ tailWord_7497454).sum := by decide
  have hdescent : baseEnd_7497454 < baseStart_7497454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497473 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_7497473 : Nat := 118140960795 + 7497473 * 2 ^ 59
def prefixEnd_7497473 : Nat := 4983230072969 + 3 ^ 40 * 7497473 * 2
def baseEnd_7497473 : Nat := 1283269114368949945369085

theorem tailTrace_7497473 : CollatzResearch.WordTrace tailWord_7497473 prefixEnd_7497473 1283269114368949945369085 := by
  unfold tailWord_7497473
  simp only [CollatzResearch.WordTrace]
  refine ⟨273455305566943262290369073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182303537044628841526912715 273455305566943262290369073)
  ·
    refine ⟨205091479175207446717776805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273455305566943262290369073 205091479175207446717776805)
    ·
      refine ⟨38454652345351396259583151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205091479175207446717776805 38454652345351396259583151)
      ·
        refine ⟨57681978518027094389374727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38454652345351396259583151 57681978518027094389374727)
        ·
          refine ⟨86522967777040641584062091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57681978518027094389374727 86522967777040641584062091)
          ·
            refine ⟨129784451665560962376093137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86522967777040641584062091 129784451665560962376093137)
            ·
              refine ⟨97338338749170721782069853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129784451665560962376093137 97338338749170721782069853)
              ·
                refine ⟨36501877030939020668276195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97338338749170721782069853 36501877030939020668276195)
                ·
                  refine ⟨54752815546408531002414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36501877030939020668276195 54752815546408531002414293)
                  ·
                    refine ⟨1283269114368949945369085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54752815546408531002414293 1283269114368949945369085)
                    ·
                      rfl

theorem cell23_7497473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_7497473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497473 prefixEnd_7497473 := by exact prefixLift 7497473
  have htrace : WordTrace (prefixWord ++ tailWord_7497473) baseStart_7497473 baseEnd_7497473 := by
    simpa [prefixWord, tailWord_7497473, baseEnd_7497473] using wordTrace_append hprefix tailTrace_7497473
  have hstable : (prefixWord ++ tailWord_7497473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497473).length < 2 ^ (prefixWord ++ tailWord_7497473).sum := by decide
  have hdescent : baseEnd_7497473 < baseStart_7497473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497483 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_7497483 : Nat := 118140960795 + 7497483 * 2 ^ 59
def prefixEnd_7497483 : Nat := 4983230072969 + 3 ^ 40 * 7497483 * 2
def baseEnd_7497483 : Nat := 3849812477913394796982209

theorem tailTrace_7497483 : CollatzResearch.WordTrace tailWord_7497483 prefixEnd_7497483 3849812477913394796982209 := by
  unfold tailWord_7497483
  simp only [CollatzResearch.WordTrace]
  refine ⟨273455670296907033998233103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182303780197938022665488735 273455670296907033998233103)
  ·
    refine ⟨410183505445360550997349655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273455670296907033998233103 410183505445360550997349655)
    ·
      refine ⟨615275258168040826496024483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410183505445360550997349655 615275258168040826496024483)
      ·
        refine ⟨922912887252061239744036725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615275258168040826496024483 922912887252061239744036725)
        ·
          refine ⟨86523083179880741226003443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 922912887252061239744036725 86523083179880741226003443)
          ·
            refine ⟨129784624769821111839005165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86523083179880741226003443 129784624769821111839005165)
            ·
              refine ⟨48669234288682916939626937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129784624769821111839005165 48669234288682916939626937)
              ·
                refine ⟨36501925716512187704720203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48669234288682916939626937 36501925716512187704720203)
                ·
                  refine ⟨54752888574768281557080305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36501925716512187704720203 54752888574768281557080305)
                  ·
                    refine ⟨41064666431076211167810229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54752888574768281557080305 41064666431076211167810229)
                    ·
                      refine ⟨3849812477913394796982209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41064666431076211167810229 3849812477913394796982209)
                      ·
                        rfl

theorem cell23_7497483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_7497483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497483 prefixEnd_7497483 := by exact prefixLift 7497483
  have htrace : WordTrace (prefixWord ++ tailWord_7497483) baseStart_7497483 baseEnd_7497483 := by
    simpa [prefixWord, tailWord_7497483, baseEnd_7497483] using wordTrace_append hprefix tailTrace_7497483
  have hstable : (prefixWord ++ tailWord_7497483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497483).length < 2 ^ (prefixWord ++ tailWord_7497483).sum := by decide
  have hdescent : baseEnd_7497483 < baseStart_7497483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497524 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_7497524 : Nat := 118140960795 + 7497524 * 2 ^ 59
def prefixEnd_7497524 : Nat := 4983230072969 + 3 ^ 40 * 7497524 * 2
def baseEnd_7497524 : Nat := 1283277843540076378856507

theorem tailTrace_7497524 : CollatzResearch.WordTrace tailWord_7497524 prefixEnd_7497524 1283277843540076378856507 := by
  unfold tailWord_7497524
  simp only [CollatzResearch.WordTrace]
  refine ⟨136728582844879249000237813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182304777126505665333650417 136728582844879249000237813)
  ·
    refine ⟨12818304641707429593772295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136728582844879249000237813 12818304641707429593772295)
    ·
      refine ⟨19227456962561144390658443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12818304641707429593772295 19227456962561144390658443)
      ·
        refine ⟨28841185443841716585987665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19227456962561144390658443 28841185443841716585987665)
        ·
          refine ⟨21630889082881287439490749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28841185443841716585987665 21630889082881287439490749)
          ·
            refine ⟨8111583406080482789809031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21630889082881287439490749 8111583406080482789809031)
            ·
              refine ⟨12167375109120724184713547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111583406080482789809031 12167375109120724184713547)
              ·
                refine ⟨18251062663681086277070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167375109120724184713547 18251062663681086277070321)
                ·
                  refine ⟨13688296997760814707802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18251062663681086277070321 13688296997760814707802741)
                  ·
                    refine ⟨1283277843540076378856507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13688296997760814707802741 1283277843540076378856507)
                    ·
                      rfl

theorem cell23_7497524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_7497524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497524 prefixEnd_7497524 := by exact prefixLift 7497524
  have htrace : WordTrace (prefixWord ++ tailWord_7497524) baseStart_7497524 baseEnd_7497524 := by
    simpa [prefixWord, tailWord_7497524, baseEnd_7497524] using wordTrace_append hprefix tailTrace_7497524
  have hstable : (prefixWord ++ tailWord_7497524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497524).length < 2 ^ (prefixWord ++ tailWord_7497524).sum := by decide
  have hdescent : baseEnd_7497524 < baseStart_7497524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497554 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_7497554 : Nat := 118140960795 + 7497554 * 2 ^ 59
def prefixEnd_7497554 : Nat := 4983230072969 + 3 ^ 40 * 7497554 * 2
def baseEnd_7497554 : Nat := 1283282978346621339731461

theorem tailTrace_7497554 : CollatzResearch.WordTrace tailWord_7497554 prefixEnd_7497554 1283282978346621339731461 := by
  unfold tailWord_7497554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68364564969912453281016929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182305506586433208749378477 68364564969912453281016929)
  ·
    refine ⟨51273423727434339960762697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68364564969912453281016929 51273423727434339960762697)
    ·
      refine ⟨38455067795575754970572023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51273423727434339960762697 38455067795575754970572023)
      ·
        refine ⟨57682601693363632455858035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38455067795575754970572023 57682601693363632455858035)
        ·
          refine ⟨86523902540045448683787053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57682601693363632455858035 86523902540045448683787053)
          ·
            refine ⟨32446463452517043256420145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86523902540045448683787053 32446463452517043256420145)
            ·
              refine ⟨24334847589387782442315109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32446463452517043256420145 24334847589387782442315109)
              ·
                refine ⟨4562783923010209207934083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24334847589387782442315109 4562783923010209207934083)
                ·
                  refine ⟨6844175884515313811901125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562783923010209207934083 6844175884515313811901125)
                  ·
                    refine ⟨1283282978346621339731461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844175884515313811901125 1283282978346621339731461)
                    ·
                      rfl

theorem cell23_7497554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_7497554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497554 prefixEnd_7497554 := by exact prefixLift 7497554
  have htrace : WordTrace (prefixWord ++ tailWord_7497554) baseStart_7497554 baseEnd_7497554 := by
    simpa [prefixWord, tailWord_7497554, baseEnd_7497554] using wordTrace_append hprefix tailTrace_7497554
  have hstable : (prefixWord ++ tailWord_7497554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497554).length < 2 ^ (prefixWord ++ tailWord_7497554).sum := by decide
  have hdescent : baseEnd_7497554 < baseStart_7497554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497567 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 6]
def baseStart_7497567 : Nat := 118140960795 + 7497567 * 2 ^ 59
def prefixEnd_7497567 : Nat := 4983230072969 + 3 ^ 40 * 7497567 * 2
def baseEnd_7497567 : Nat := 427761734476485829814647

theorem tailTrace_7497567 : CollatzResearch.WordTrace tailWord_7497567 prefixEnd_7497567 427761734476485829814647 := by
  unfold tailWord_7497567
  simp only [CollatzResearch.WordTrace]
  refine ⟨273458734028602716344290955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182305822685735144229527303 273458734028602716344290955)
  ·
    refine ⟨410188101042904074516436433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273458734028602716344290955 410188101042904074516436433)
    ·
      refine ⟨307641075782178055887327325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410188101042904074516436433 307641075782178055887327325)
      ·
        refine ⟨115365403418316770957747747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307641075782178055887327325 115365403418316770957747747)
        ·
          refine ⟨173048105127475156436621621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115365403418316770957747747 173048105127475156436621621)
          ·
            refine ⟨16223259855700795915933277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173048105127475156436621621 16223259855700795915933277)
            ·
              refine ⟨6083722445887798468474979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16223259855700795915933277 6083722445887798468474979)
              ·
                refine ⟨9125583668831697702712469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083722445887798468474979 9125583668831697702712469)
                ·
                  refine ⟨427761734476485829814647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9125583668831697702712469 427761734476485829814647)
                  ·
                    rfl

theorem cell23_7497567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 6].length) (baseStart_7497567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497567 prefixEnd_7497567 := by exact prefixLift 7497567
  have htrace : WordTrace (prefixWord ++ tailWord_7497567) baseStart_7497567 baseEnd_7497567 := by
    simpa [prefixWord, tailWord_7497567, baseEnd_7497567] using wordTrace_append hprefix tailTrace_7497567
  have hstable : (prefixWord ++ tailWord_7497567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497567).length < 2 ^ (prefixWord ++ tailWord_7497567).sum := by decide
  have hdescent : baseEnd_7497567 < baseStart_7497567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497587 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 2, 3, 2]
def baseStart_7497587 : Nat := 118140960795 + 7497587 * 2 ^ 59
def prefixEnd_7497587 : Nat := 4983230072969 + 3 ^ 40 * 7497587 * 2
def baseEnd_7497587 : Nat := 3849865879901462390081731

theorem tailTrace_7497587 : CollatzResearch.WordTrace tailWord_7497587 prefixEnd_7497587 3849865879901462390081731 := by
  unfold tailWord_7497587
  simp only [CollatzResearch.WordTrace]
  refine ⟨273459463488530259760019015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182306308992353506506679343 273459463488530259760019015)
  ·
    refine ⟨410189195232795389640028523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273459463488530259760019015 410189195232795389640028523)
    ·
      refine ⟨615283792849193084460042785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410189195232795389640028523 615283792849193084460042785)
      ·
        refine ⟨461462844636894813345032089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615283792849193084460042785 461462844636894813345032089)
        ·
          refine ⟨346097133477671110008774067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461462844636894813345032089 346097133477671110008774067)
          ·
            refine ⟨519145700216506665013161101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346097133477671110008774067 519145700216506665013161101)
            ·
              refine ⟨194679637581189999379935413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519145700216506665013161101 194679637581189999379935413)
              ·
                refine ⟨18251216023236562441868945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194679637581189999379935413 18251216023236562441868945)
                ·
                  refine ⟨13688412017427421831401709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18251216023236562441868945 13688412017427421831401709)
                  ·
                    refine ⟨5133154506535283186775641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13688412017427421831401709 5133154506535283186775641)
                    ·
                      refine ⟨3849865879901462390081731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133154506535283186775641 3849865879901462390081731)
                      ·
                        rfl

theorem cell23_7497587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3, 2].length) (baseStart_7497587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497587 prefixEnd_7497587 := by exact prefixLift 7497587
  have htrace : WordTrace (prefixWord ++ tailWord_7497587) baseStart_7497587 baseEnd_7497587 := by
    simpa [prefixWord, tailWord_7497587, baseEnd_7497587] using wordTrace_append hprefix tailTrace_7497587
  have hstable : (prefixWord ++ tailWord_7497587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497587).length < 2 ^ (prefixWord ++ tailWord_7497587).sum := by decide
  have hdescent : baseEnd_7497587 < baseStart_7497587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497631 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 1, 5]
def baseStart_7497631 : Nat := 118140960795 + 7497631 * 2 ^ 59
def prefixEnd_7497631 : Nat := 4983230072969 + 3 ^ 40 * 7497631 * 2
def baseEnd_7497631 : Nat := 1283296157683420072643843

theorem tailTrace_7497631 : CollatzResearch.WordTrace tailWord_7497631 prefixEnd_7497631 1283296157683420072643843 := by
  unfold tailWord_7497631
  simp only [CollatzResearch.WordTrace]
  refine ⟨273461068300370855274620747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182307378866913903516413831 273461068300370855274620747)
  ·
    refine ⟨410191602450556282911931121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273461068300370855274620747 410191602450556282911931121)
    ·
      refine ⟨307643701837917212183948341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410191602450556282911931121 307643701837917212183948341)
      ·
        refine ⟨28841597047304738642245157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307643701837917212183948341 28841597047304738642245157)
        ·
          refine ⟨5407799446369638495420967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28841597047304738642245157 5407799446369638495420967)
          ·
            refine ⟨8111699169554457743131451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407799446369638495420967 8111699169554457743131451)
            ·
              refine ⟨12167548754331686614697177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111699169554457743131451 12167548754331686614697177)
              ·
                refine ⟨9125661565748764961022883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12167548754331686614697177 9125661565748764961022883)
                ·
                  refine ⟨13688492348623147441534325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125661565748764961022883 13688492348623147441534325)
                  ·
                    refine ⟨1283296157683420072643843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13688492348623147441534325 1283296157683420072643843)
                    ·
                      rfl

theorem cell23_7497631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_7497631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497631 prefixEnd_7497631 := by exact prefixLift 7497631
  have htrace : WordTrace (prefixWord ++ tailWord_7497631) baseStart_7497631 baseEnd_7497631 := by
    simpa [prefixWord, tailWord_7497631, baseEnd_7497631] using wordTrace_append hprefix tailTrace_7497631
  have hstable : (prefixWord ++ tailWord_7497631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497631).length < 2 ^ (prefixWord ++ tailWord_7497631).sum := by decide
  have hdescent : baseEnd_7497631 < baseStart_7497631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497634 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_7497634 : Nat := 118140960795 + 7497634 * 2 ^ 59
def prefixEnd_7497634 : Nat := 4983230072969 + 3 ^ 40 * 7497634 * 2
def baseEnd_7497634 : Nat := 3849890013492223706194015

theorem tailTrace_7497634 : CollatzResearch.WordTrace tailWord_7497634 prefixEnd_7497634 3849890013492223706194015 := by
  unfold tailWord_7497634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68365294429839996696744989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182307451812906657857986637 68365294429839996696744989)
  ·
    refine ⟨25636985411189998761279371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68365294429839996696744989 25636985411189998761279371)
    ·
      refine ⟨38455478116784998141919057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25636985411189998761279371 38455478116784998141919057)
      ·
        refine ⟨28841608587588748606439293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38455478116784998141919057 28841608587588748606439293)
        ·
          refine ⟨10815603220345780727414735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28841608587588748606439293 10815603220345780727414735)
          ·
            refine ⟨16223404830518671091122103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10815603220345780727414735 16223404830518671091122103)
            ·
              refine ⟨24335107245778006636683155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16223404830518671091122103 24335107245778006636683155)
              ·
                refine ⟨36502660868667009955024733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24335107245778006636683155 36502660868667009955024733)
                ·
                  refine ⟨13688497825750128733134275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36502660868667009955024733 13688497825750128733134275)
                  ·
                    refine ⟨20532746738625193099701413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13688497825750128733134275 20532746738625193099701413)
                    ·
                      refine ⟨3849890013492223706194015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20532746738625193099701413 3849890013492223706194015)
                      ·
                        rfl

theorem cell23_7497634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_7497634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497634 prefixEnd_7497634 := by exact prefixLift 7497634
  have htrace : WordTrace (prefixWord ++ tailWord_7497634) baseStart_7497634 baseEnd_7497634 := by
    simpa [prefixWord, tailWord_7497634, baseEnd_7497634] using wordTrace_append hprefix tailTrace_7497634
  have hstable : (prefixWord ++ tailWord_7497634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497634).length < 2 ^ (prefixWord ++ tailWord_7497634).sum := by decide
  have hdescent : baseEnd_7497634 < baseStart_7497634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497651 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 1, 2, 2]
def baseStart_7497651 : Nat := 118140960795 + 7497651 * 2 ^ 59
def prefixEnd_7497651 : Nat := 4983230072969 + 3 ^ 40 * 7497651 * 2
def baseEnd_7497651 : Nat := 3849898742663350139681437

theorem tailTrace_7497651 : CollatzResearch.WordTrace tailWord_7497651 prefixEnd_7497651 3849898742663350139681437 := by
  unfold tailWord_7497651
  simp only [CollatzResearch.WordTrace]
  refine ⟨273461797760298398690348807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182307865173532265793565871 273461797760298398690348807)
  ·
    refine ⟨410192696640447598035523211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273461797760298398690348807 410192696640447598035523211)
    ·
      refine ⟨615289044960671397053284817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410192696640447598035523211 615289044960671397053284817)
      ·
        refine ⟨461466783720503547789963613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615289044960671397053284817 461466783720503547789963613)
        ·
          refine ⟨173050043895188830421236355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461466783720503547789963613 173050043895188830421236355)
          ·
            refine ⟨259575065842783245631854533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173050043895188830421236355 259575065842783245631854533)
            ·
              refine ⟨48670324845521858555972725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259575065842783245631854533 48670324845521858555972725)
              ·
                refine ⟨4562842954267674239622443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48670324845521858555972725 4562842954267674239622443)
                ·
                  refine ⟨6844264431401511359433665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562842954267674239622443 6844264431401511359433665)
                  ·
                    refine ⟨5133198323551133519575249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844264431401511359433665 5133198323551133519575249)
                    ·
                      refine ⟨3849898742663350139681437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133198323551133519575249 3849898742663350139681437)
                      ·
                        rfl

theorem cell23_7497651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 2, 2].length) (baseStart_7497651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497651 prefixEnd_7497651 := by exact prefixLift 7497651
  have htrace : WordTrace (prefixWord ++ tailWord_7497651) baseStart_7497651 baseEnd_7497651 := by
    simpa [prefixWord, tailWord_7497651, baseEnd_7497651] using wordTrace_append hprefix tailTrace_7497651
  have hstable : (prefixWord ++ tailWord_7497651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497651).length < 2 ^ (prefixWord ++ tailWord_7497651).sum := by decide
  have hdescent : baseEnd_7497651 < baseStart_7497651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497684 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7497684 : Nat := 118140960795 + 7497684 * 2 ^ 59
def prefixEnd_7497684 : Nat := 4983230072969 + 3 ^ 40 * 7497684 * 2
def baseEnd_7497684 : Nat := 3849915687524948510568785

theorem tailTrace_7497684 : CollatzResearch.WordTrace tailWord_7497684 prefixEnd_7497684 3849915687524948510568785 := by
  unfold tailWord_7497684
  simp only [CollatzResearch.WordTrace]
  refine ⟨136731500684589422663150053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182308667579452563550866737 136731500684589422663150053)
  ·
    refine ⟨25637156378360516749340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136731500684589422663150053 25637156378360516749340635)
    ·
      refine ⟨38455734567540775124010953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25637156378360516749340635 38455734567540775124010953)
      ·
        refine ⟨28841800925655581343008215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38455734567540775124010953 28841800925655581343008215)
        ·
          refine ⟨43262701388483372014512323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28841800925655581343008215 43262701388483372014512323)
          ·
            refine ⟨64894052082725058021768485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43262701388483372014512323 64894052082725058021768485)
            ·
              refine ⟨12167634765510948379081591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64894052082725058021768485 12167634765510948379081591)
              ·
                refine ⟨18251452148266422568622387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167634765510948379081591 18251452148266422568622387)
                ·
                  refine ⟨27377178222399633852933581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18251452148266422568622387 27377178222399633852933581)
                  ·
                    refine ⟨10266441833399862694850093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27377178222399633852933581 10266441833399862694850093)
                    ·
                      refine ⟨3849915687524948510568785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10266441833399862694850093 3849915687524948510568785)
                      ·
                        rfl

theorem cell23_7497684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7497684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497684 prefixEnd_7497684 := by exact prefixLift 7497684
  have htrace : WordTrace (prefixWord ++ tailWord_7497684) baseStart_7497684 baseEnd_7497684 := by
    simpa [prefixWord, tailWord_7497684, baseEnd_7497684] using wordTrace_append hprefix tailTrace_7497684
  have hstable : (prefixWord ++ tailWord_7497684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497684).length < 2 ^ (prefixWord ++ tailWord_7497684).sum := by decide
  have hdescent : baseEnd_7497684 < baseStart_7497684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497700 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_7497700 : Nat := 118140960795 + 7497700 * 2 ^ 59
def prefixEnd_7497700 : Nat := 4983230072969 + 3 ^ 40 * 7497700 * 2
def baseEnd_7497700 : Nat := 1283307967738473482656237

theorem tailTrace_7497700 : CollatzResearch.WordTrace tailWord_7497700 prefixEnd_7497700 1283307967738473482656237 := by
  unfold tailWord_7497700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136731792468560440029441277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182309056624747253372588369 136731792468560440029441277)
  ·
    refine ⟨51274422175710165011040479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136731792468560440029441277 51274422175710165011040479)
    ·
      refine ⟨76911633263565247516560719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51274422175710165011040479 76911633263565247516560719)
      ·
        refine ⟨115367449895347871274841079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76911633263565247516560719 115367449895347871274841079)
        ·
          refine ⟨173051174843021806912261619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115367449895347871274841079 173051174843021806912261619)
          ·
            refine ⟨259576762264532710368392429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173051174843021806912261619 259576762264532710368392429)
            ·
              refine ⟨97341285849199766388147161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259576762264532710368392429 97341285849199766388147161)
              ·
                refine ⟨73005964386899824791110371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97341285849199766388147161 73005964386899824791110371)
                ·
                  refine ⟨109508946580349737186665557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73005964386899824791110371 109508946580349737186665557)
                  ·
                    refine ⟨1283307967738473482656237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109508946580349737186665557 1283307967738473482656237)
                    ·
                      rfl

theorem cell23_7497700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_7497700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497700 prefixEnd_7497700 := by exact prefixLift 7497700
  have htrace : WordTrace (prefixWord ++ tailWord_7497700) baseStart_7497700 baseEnd_7497700 := by
    simpa [prefixWord, tailWord_7497700, baseEnd_7497700] using wordTrace_append hprefix tailTrace_7497700
  have hstable : (prefixWord ++ tailWord_7497700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497700).length < 2 ^ (prefixWord ++ tailWord_7497700).sum := by decide
  have hdescent : baseEnd_7497700 < baseStart_7497700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497777 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_7497777 : Nat := 118140960795 + 7497777 * 2 ^ 59
def prefixEnd_7497777 : Nat := 4983230072969 + 3 ^ 40 * 7497777 * 2
def baseEnd_7497777 : Nat := 1283321147075272215568619

theorem tailTrace_7497777 : CollatzResearch.WordTrace tailWord_7497777 prefixEnd_7497777 1283321147075272215568619 := by
  unfold tailWord_7497777
  simp only [CollatzResearch.WordTrace]
  refine ⟨273466393357841922209435585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182310928905227948139623723 273466393357841922209435585)
  ·
    refine ⟨205099795018381441657076689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273466393357841922209435585 205099795018381441657076689)
    ·
      refine ⟨153824846263786081242807517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205099795018381441657076689 153824846263786081242807517)
      ·
        refine ⟨57684317348919780466052819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153824846263786081242807517 57684317348919780466052819)
        ·
          refine ⟨86526476023379670699079229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57684317348919780466052819 86526476023379670699079229)
          ·
            refine ⟨32447428508767376512154711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86526476023379670699079229 32447428508767376512154711)
            ·
              refine ⟨48671142763151064768232067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32447428508767376512154711 48671142763151064768232067)
              ·
                refine ⟨73006714144726597152348101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48671142763151064768232067 73006714144726597152348101)
                ·
                  refine ⟨13688758902136236966065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73006714144726597152348101 13688758902136236966065269)
                  ·
                    refine ⟨1283321147075272215568619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13688758902136236966065269 1283321147075272215568619)
                    ·
                      rfl

theorem cell23_7497777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_7497777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497777 prefixEnd_7497777 := by exact prefixLift 7497777
  have htrace : WordTrace (prefixWord ++ tailWord_7497777) baseStart_7497777 baseEnd_7497777 := by
    simpa [prefixWord, tailWord_7497777, baseEnd_7497777] using wordTrace_append hprefix tailTrace_7497777
  have hstable : (prefixWord ++ tailWord_7497777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497777).length < 2 ^ (prefixWord ++ tailWord_7497777).sum := by decide
  have hdescent : baseEnd_7497777 < baseStart_7497777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497797 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_7497797 : Nat := 118140960795 + 7497797 * 2 ^ 59
def prefixEnd_7497797 : Nat := 4983230072969 + 3 ^ 40 * 7497797 * 2
def baseEnd_7497797 : Nat := 3849973710838906568455765

theorem tailTrace_7497797 : CollatzResearch.WordTrace tailWord_7497797 prefixEnd_7497797 3849973710838906568455765 := by
  unfold tailWord_7497797
  simp only [CollatzResearch.WordTrace]
  refine ⟨273467122817769465625163645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182311415211846310416775763 273467122817769465625163645)
  ·
    refine ⟨102550171056663549609436367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273467122817769465625163645 102550171056663549609436367)
    ·
      refine ⟨153825256584995324414154551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102550171056663549609436367 153825256584995324414154551)
      ·
        refine ⟨230737884877492986621231827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153825256584995324414154551 230737884877492986621231827)
        ·
          refine ⟨346106827316239479931847741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230737884877492986621231827 346106827316239479931847741)
          ·
            refine ⟨129790060243589804974442903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346106827316239479931847741 129790060243589804974442903)
            ·
              refine ⟨194685090365384707461664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129790060243589804974442903 194685090365384707461664355)
              ·
                refine ⟨292027635548077061192496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194685090365384707461664355 292027635548077061192496533)
                ·
                  refine ⟨13688795416316112243398275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292027635548077061192496533 13688795416316112243398275)
                  ·
                    refine ⟨20533193124474168365097413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13688795416316112243398275 20533193124474168365097413)
                    ·
                      refine ⟨3849973710838906568455765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20533193124474168365097413 3849973710838906568455765)
                      ·
                        rfl

theorem cell23_7497797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_7497797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497797 prefixEnd_7497797 := by exact prefixLift 7497797
  have htrace : WordTrace (prefixWord ++ tailWord_7497797) baseStart_7497797 baseEnd_7497797 := by
    simpa [prefixWord, tailWord_7497797, baseEnd_7497797] using wordTrace_append hprefix tailTrace_7497797
  have hstable : (prefixWord ++ tailWord_7497797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497797).length < 2 ^ (prefixWord ++ tailWord_7497797).sum := by decide
  have hdescent : baseEnd_7497797 < baseStart_7497797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497841 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 1, 4]
def baseStart_7497841 : Nat := 118140960795 + 7497841 * 2 ^ 59
def prefixEnd_7497841 : Nat := 4983230072969 + 3 ^ 40 * 7497841 * 2
def baseEnd_7497841 : Nat := 1283332101329234798768521

theorem tailTrace_7497841 : CollatzResearch.WordTrace tailWord_7497841 prefixEnd_7497841 1283332101329234798768521 := by
  unfold tailWord_7497841
  simp only [CollatzResearch.WordTrace]
  refine ⟨273468727629610061139765377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182312485086406707426510251 273468727629610061139765377)
  ·
    refine ⟨205101545722207545854824033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273468727629610061139765377 205101545722207545854824033)
    ·
      refine ⟨153826159291655659391118025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205101545722207545854824033 153826159291655659391118025)
      ·
        refine ⟨115369619468741744543338519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153826159291655659391118025 115369619468741744543338519)
        ·
          refine ⟨173054429203112616815007779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115369619468741744543338519 173054429203112616815007779)
          ·
            refine ⟨259581643804668925222511669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173054429203112616815007779 259581643804668925222511669)
            ·
              refine ⟨24335779106687711739610469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259581643804668925222511669 24335779106687711739610469)
              ·
                refine ⟨4562958582503945951176963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24335779106687711739610469 4562958582503945951176963)
                ·
                  refine ⟨6844437873755918926765445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562958582503945951176963 6844437873755918926765445)
                  ·
                    refine ⟨1283332101329234798768521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844437873755918926765445 1283332101329234798768521)
                    ·
                      rfl

theorem cell23_7497841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_7497841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497841 prefixEnd_7497841 := by exact prefixLift 7497841
  have htrace : WordTrace (prefixWord ++ tailWord_7497841) baseStart_7497841 baseEnd_7497841 := by
    simpa [prefixWord, tailWord_7497841, baseEnd_7497841] using wordTrace_append hprefix tailTrace_7497841
  have hstable : (prefixWord ++ tailWord_7497841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497841).length < 2 ^ (prefixWord ++ tailWord_7497841).sum := by decide
  have hdescent : baseEnd_7497841 < baseStart_7497841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497904 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2]
def baseStart_7497904 : Nat := 118140960795 + 7497904 * 2 ^ 59
def prefixEnd_7497904 : Nat := 4983230072969 + 3 ^ 40 * 7497904 * 2
def baseEnd_7497904 : Nat := 3850028653268937649817773

theorem tailTrace_7497904 : CollatzResearch.WordTrace tailWord_7497904 prefixEnd_7497904 3850028653268937649817773 := by
  unfold tailWord_7497904
  simp only [CollatzResearch.WordTrace]
  refine ⟨136735512714190911449654383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182314016952254548599539177 136735512714190911449654383)
  ·
    refine ⟨205103269071286367174481575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136735512714190911449654383 205103269071286367174481575)
    ·
      refine ⟨307654903606929550761722363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205103269071286367174481575 307654903606929550761722363)
      ·
        refine ⟨461482355410394326142583545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307654903606929550761722363 461482355410394326142583545)
        ·
          refine ⟨346111766557795744606937659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461482355410394326142583545 346111766557795744606937659)
          ·
            refine ⟨519167649836693616910406489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346111766557795744606937659 519167649836693616910406489)
            ·
              refine ⟨389375737377520212682804867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519167649836693616910406489 389375737377520212682804867)
              ·
                refine ⟨584063606066280319024207301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389375737377520212682804867 584063606066280319024207301)
                ·
                  refine ⟨109511926137427559817038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584063606066280319024207301 109511926137427559817038869)
                  ·
                    refine ⟨5133371537691916866423697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109511926137427559817038869 5133371537691916866423697)
                    ·
                      refine ⟨3850028653268937649817773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133371537691916866423697 3850028653268937649817773)
                      ·
                        rfl

theorem cell23_7497904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 6, 2].length) (baseStart_7497904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497904 prefixEnd_7497904 := by exact prefixLift 7497904
  have htrace : WordTrace (prefixWord ++ tailWord_7497904) baseStart_7497904 baseEnd_7497904 := by
    simpa [prefixWord, tailWord_7497904, baseEnd_7497904] using wordTrace_append hprefix tailTrace_7497904
  have hstable : (prefixWord ++ tailWord_7497904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497904).length < 2 ^ (prefixWord ++ tailWord_7497904).sum := by decide
  have hdescent : baseEnd_7497904 < baseStart_7497904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497914 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_7497914 : Nat := 118140960795 + 7497914 * 2 ^ 59
def prefixEnd_7497914 : Nat := 4983230072969 + 3 ^ 40 * 7497914 * 2
def baseEnd_7497914 : Nat := 1283344596025160870230909

theorem tailTrace_7497914 : CollatzResearch.WordTrace tailWord_7497914 prefixEnd_7497914 1283344596025160870230909 := by
  unfold tailWord_7497914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68367847539586398651793199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182314260105563729738115197 68367847539586398651793199)
  ·
    refine ⟨102551771309379597977689799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68367847539586398651793199 102551771309379597977689799)
    ·
      refine ⟨153827656964069396966534699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102551771309379597977689799 153827656964069396966534699)
      ·
        refine ⟨230741485446104095449802049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153827656964069396966534699 230741485446104095449802049)
        ·
          refine ⟨173056114084578071587351537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230741485446104095449802049 173056114084578071587351537)
          ·
            refine ⟨129792085563433553690513653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173056114084578071587351537 129792085563433553690513653)
            ·
              refine ⟨12168008021571895658485655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129792085563433553690513653 12168008021571895658485655)
              ·
                refine ⟨18252012032357843487728483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168008021571895658485655 18252012032357843487728483)
                ·
                  refine ⟨27378018048536765231592725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18252012032357843487728483 27378018048536765231592725)
                  ·
                    refine ⟨1283344596025160870230909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27378018048536765231592725 1283344596025160870230909)
                    ·
                      rfl

theorem cell23_7497914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_7497914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497914 prefixEnd_7497914 := by exact prefixLift 7497914
  have htrace : WordTrace (prefixWord ++ tailWord_7497914) baseStart_7497914 baseEnd_7497914 := by
    simpa [prefixWord, tailWord_7497914, baseEnd_7497914] using wordTrace_append hprefix tailTrace_7497914
  have hstable : (prefixWord ++ tailWord_7497914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497914).length < 2 ^ (prefixWord ++ tailWord_7497914).sum := by decide
  have hdescent : baseEnd_7497914 < baseStart_7497914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497918 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_7497918 : Nat := 118140960795 + 7497918 * 2 ^ 59
def prefixEnd_7497918 : Nat := 4983230072969 + 3 ^ 40 * 7497918 * 2
def baseEnd_7497918 : Nat := 1283345280666033531680903

theorem tailTrace_7497918 : CollatzResearch.WordTrace tailWord_7497918 prefixEnd_7497918 1283345280666033531680903 := by
  unfold tailWord_7497918
  simp only [CollatzResearch.WordTrace]
  refine ⟨34183942006291387911289801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182314357366887402193545605 34183942006291387911289801)
  ·
    refine ⟨25637956504718540933467351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34183942006291387911289801 25637956504718540933467351)
    ·
      refine ⟨38456934757077811400201027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25637956504718540933467351 38456934757077811400201027)
      ·
        refine ⟨57685402135616717100301541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38456934757077811400201027 57685402135616717100301541)
        ·
          refine ⟨10816012900428134456306539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57685402135616717100301541 10816012900428134456306539)
          ·
            refine ⟨16224019350642201684459809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816012900428134456306539 16224019350642201684459809)
            ·
              refine ⟨12168014512981651263344857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16224019350642201684459809 12168014512981651263344857)
              ·
                refine ⟨9126010884736238447508643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168014512981651263344857 9126010884736238447508643)
                ·
                  refine ⟨13689016327104357671262965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126010884736238447508643 13689016327104357671262965)
                  ·
                    refine ⟨1283345280666033531680903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13689016327104357671262965 1283345280666033531680903)
                    ·
                      rfl

theorem cell23_7497918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_7497918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497918 prefixEnd_7497918 := by exact prefixLift 7497918
  have htrace : WordTrace (prefixWord ++ tailWord_7497918) baseStart_7497918 baseEnd_7497918 := by
    simpa [prefixWord, tailWord_7497918, baseEnd_7497918] using wordTrace_append hprefix tailTrace_7497918
  have hstable : (prefixWord ++ tailWord_7497918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497918).length < 2 ^ (prefixWord ++ tailWord_7497918).sum := by decide
  have hdescent : baseEnd_7497918 < baseStart_7497918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497944 : List Nat := [2, 1, 2, 2, 4, 3, 9]
def baseStart_7497944 : Nat := 118140960795 + 7497944 * 2 ^ 59
def prefixEnd_7497944 : Nat := 4983230072969 + 3 ^ 40 * 7497944 * 2
def baseEnd_7497944 : Nat := 47531471512285401152069

theorem tailTrace_7497944 : CollatzResearch.WordTrace tailWord_7497944 prefixEnd_7497944 47531471512285401152069 := by
  unfold tailWord_7497944
  simp only [CollatzResearch.WordTrace]
  refine ⟨136736242174118454865382443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182314989565491273153843257 136736242174118454865382443)
  ·
    refine ⟨205104363261177682298073665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136736242174118454865382443 205104363261177682298073665)
    ·
      refine ⟨153828272445883261723555249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205104363261177682298073665 153828272445883261723555249)
      ·
        refine ⟨115371204334412446292666437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153828272445883261723555249 115371204334412446292666437)
        ·
          refine ⟨21632100812702333679874957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115371204334412446292666437 21632100812702333679874957)
          ·
            refine ⟨8112037804763375129953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21632100812702333679874957 8112037804763375129953109)
            ·
              refine ⟨47531471512285401152069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8112037804763375129953109 47531471512285401152069)
              ·
                rfl

theorem cell23_7497944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 9].length) (baseStart_7497944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497944 prefixEnd_7497944 := by exact prefixLift 7497944
  have htrace : WordTrace (prefixWord ++ tailWord_7497944) baseStart_7497944 baseEnd_7497944 := by
    simpa [prefixWord, tailWord_7497944, baseEnd_7497944] using wordTrace_append hprefix tailTrace_7497944
  have hstable : (prefixWord ++ tailWord_7497944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497944).length < 2 ^ (prefixWord ++ tailWord_7497944).sum := by decide
  have hdescent : baseEnd_7497944 < baseStart_7497944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_7497947 : Nat := 118140960795 + 7497947 * 2 ^ 59
def prefixEnd_7497947 : Nat := 4983230072969 + 3 ^ 40 * 7497947 * 2
def baseEnd_7497947 : Nat := 3850050732937080981580075

theorem tailTrace_7497947 : CollatzResearch.WordTrace tailWord_7497947 prefixEnd_7497947 3850050732937080981580075 := by
  unfold tailWord_7497947
  simp only [CollatzResearch.WordTrace]
  refine ⟨273472593767226041243124095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182315062511484027495416063 273472593767226041243124095)
  ·
    refine ⟨410208890650839061864686143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273472593767226041243124095 410208890650839061864686143)
    ·
      refine ⟨615313335976258592797029215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410208890650839061864686143 615313335976258592797029215)
      ·
        refine ⟨922970003964387889195543823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615313335976258592797029215 922970003964387889195543823)
        ·
          refine ⟨1384455005946581833793315735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922970003964387889195543823 1384455005946581833793315735)
          ·
            refine ⟨2076682508919872750689973603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384455005946581833793315735 2076682508919872750689973603)
            ·
              refine ⟨3115023763379809126034960405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076682508919872750689973603 3115023763379809126034960405)
              ·
                refine ⟨146016738908428552782888769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3115023763379809126034960405 146016738908428552782888769)
                ·
                  refine ⟨109512554181321414587166577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146016738908428552782888769 109512554181321414587166577)
                  ·
                    refine ⟨82134415635991060940374933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109512554181321414587166577 82134415635991060940374933)
                    ·
                      refine ⟨3850050732937080981580075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82134415635991060940374933 3850050732937080981580075)
                      ·
                        rfl

theorem cell23_7497947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_7497947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497947 prefixEnd_7497947 := by exact prefixLift 7497947
  have htrace : WordTrace (prefixWord ++ tailWord_7497947) baseStart_7497947 baseEnd_7497947 := by
    simpa [prefixWord, tailWord_7497947, baseEnd_7497947] using wordTrace_append hprefix tailTrace_7497947
  have hstable : (prefixWord ++ tailWord_7497947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497947).length < 2 ^ (prefixWord ++ tailWord_7497947).sum := by decide
  have hdescent : baseEnd_7497947 < baseStart_7497947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7497988 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7497988 : Nat := 118140960795 + 7497988 * 2 ^ 59
def prefixEnd_7497988 : Nat := 4983230072969 + 3 ^ 40 * 7497988 * 2
def baseEnd_7497988 : Nat := 3850071785643915321167387

theorem tailTrace_7497988 : CollatzResearch.WordTrace tailWord_7497988 prefixEnd_7497988 3850071785643915321167387 := by
  unfold tailWord_7497988
  simp only [CollatzResearch.WordTrace]
  refine ⟨136737044580038752622683309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182316059440051670163577745 136737044580038752622683309)
  ·
    refine ⟨51276391717514532233506241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136737044580038752622683309 51276391717514532233506241)
    ·
      refine ⟨38457293788135899175129681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51276391717514532233506241 38457293788135899175129681)
      ·
        refine ⟨28842970341101924381347261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38457293788135899175129681 28842970341101924381347261)
        ·
          refine ⟨10816113877913221643005223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28842970341101924381347261 10816113877913221643005223)
          ·
            refine ⟨16224170816869832464507835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816113877913221643005223 16224170816869832464507835)
            ·
              refine ⟨24336256225304748696761753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16224170816869832464507835 24336256225304748696761753)
              ·
                refine ⟨18252192168978561522571315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24336256225304748696761753 18252192168978561522571315)
                ·
                  refine ⟨27378288253467842283856973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18252192168978561522571315 27378288253467842283856973)
                  ·
                    refine ⟨10266858095050440856446365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27378288253467842283856973 10266858095050440856446365)
                    ·
                      refine ⟨3850071785643915321167387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10266858095050440856446365 3850071785643915321167387)
                      ·
                        rfl

theorem cell23_7497988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7497988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7497988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7497988 prefixEnd_7497988 := by exact prefixLift 7497988
  have htrace : WordTrace (prefixWord ++ tailWord_7497988) baseStart_7497988 baseEnd_7497988 := by
    simpa [prefixWord, tailWord_7497988, baseEnd_7497988] using wordTrace_append hprefix tailTrace_7497988
  have hstable : (prefixWord ++ tailWord_7497988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7497988).length < 2 ^ (prefixWord ++ tailWord_7497988).sum := by decide
  have hdescent : baseEnd_7497988 < baseStart_7497988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7497988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498021 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_7498021 : Nat := 118140960795 + 7498021 * 2 ^ 59
def prefixEnd_7498021 : Nat := 4983230072969 + 3 ^ 40 * 7498021 * 2
def baseEnd_7498021 : Nat := 1283362910168504564018245

theorem tailTrace_7498021 : CollatzResearch.WordTrace tailWord_7498021 prefixEnd_7498021 1283362910168504564018245 := by
  unfold tailWord_7498021
  simp only [CollatzResearch.WordTrace]
  refine ⟨273475292768957951881317917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182316861845971967920878611 273475292768957951881317917)
  ·
    refine ⟨102553234788359231955494219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273475292768957951881317917 102553234788359231955494219)
    ·
      refine ⟨153829852182538847933241329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102553234788359231955494219 153829852182538847933241329)
      ·
        refine ⟨115372389136904135949930997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153829852182538847933241329 115372389136904135949930997)
        ·
          refine ⟨10816161481584762745306031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115372389136904135949930997 10816161481584762745306031)
          ·
            refine ⟨16224242222377144117959047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10816161481584762745306031 16224242222377144117959047)
            ·
              refine ⟨24336363333565716176938571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16224242222377144117959047 24336363333565716176938571)
              ·
                refine ⟨36504545000348574265407857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24336363333565716176938571 36504545000348574265407857)
                ·
                  refine ⟨27378408750261430699055893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36504545000348574265407857 27378408750261430699055893)
                  ·
                    refine ⟨1283362910168504564018245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27378408750261430699055893 1283362910168504564018245)
                    ·
                      rfl

theorem cell23_7498021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_7498021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498021 prefixEnd_7498021 := by exact prefixLift 7498021
  have htrace : WordTrace (prefixWord ++ tailWord_7498021) baseStart_7498021 baseEnd_7498021 := by
    simpa [prefixWord, tailWord_7498021, baseEnd_7498021] using wordTrace_append hprefix tailTrace_7498021
  have hstable : (prefixWord ++ tailWord_7498021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498021).length < 2 ^ (prefixWord ++ tailWord_7498021).sum := by decide
  have hdescent : baseEnd_7498021 < baseStart_7498021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498049 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7498049 : Nat := 118140960795 + 7498049 * 2 ^ 59
def prefixEnd_7498049 : Nat := 4983230072969 + 3 ^ 40 * 7498049 * 2
def baseEnd_7498049 : Nat := 3850103107963839582504607

theorem tailTrace_7498049 : CollatzResearch.WordTrace tailWord_7498049 prefixEnd_7498049 3850103107963839582504607 := by
  unfold tailWord_7498049
  simp only [CollatzResearch.WordTrace]
  refine ⟨273476314012856512663337201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182317542675237675108891467 273476314012856512663337201)
  ·
    refine ⟨205107235509642384497502901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273476314012856512663337201 205107235509642384497502901)
    ·
      refine ⟨19228803329028973546640897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205107235509642384497502901 19228803329028973546640897)
      ·
        refine ⟨14421602496771730159980673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19228803329028973546640897 14421602496771730159980673)
        ·
          refine ⟨10816201872578797619985505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14421602496771730159980673 10816201872578797619985505)
          ·
            refine ⟨8112151404434098214989129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10816201872578797619985505 8112151404434098214989129)
            ·
              refine ⟨6084113553325573661241847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112151404434098214989129 6084113553325573661241847)
              ·
                refine ⟨9126170329988360491862771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084113553325573661241847 9126170329988360491862771)
                ·
                  refine ⟨13689255494982540737794157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126170329988360491862771 13689255494982540737794157)
                  ·
                    refine ⟨5133470810618452776672809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13689255494982540737794157 5133470810618452776672809)
                    ·
                      refine ⟨3850103107963839582504607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133470810618452776672809 3850103107963839582504607)
                      ·
                        rfl

theorem cell23_7498049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7498049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498049 prefixEnd_7498049 := by exact prefixLift 7498049
  have htrace : WordTrace (prefixWord ++ tailWord_7498049) baseStart_7498049 baseEnd_7498049 := by
    simpa [prefixWord, tailWord_7498049, baseEnd_7498049] using wordTrace_append hprefix tailTrace_7498049
  have hstable : (prefixWord ++ tailWord_7498049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498049).length < 2 ^ (prefixWord ++ tailWord_7498049).sum := by decide
  have hdescent : baseEnd_7498049 < baseStart_7498049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498051 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 5]
def baseStart_7498051 : Nat := 118140960795 + 7498051 * 2 ^ 59
def prefixEnd_7498051 : Nat := 4983230072969 + 3 ^ 40 * 7498051 * 2
def baseEnd_7498051 : Nat := 427789348325016508297733

theorem tailTrace_7498051 : CollatzResearch.WordTrace tailWord_7498051 prefixEnd_7498051 427789348325016508297733 := by
  unfold tailWord_7498051
  simp only [CollatzResearch.WordTrace]
  refine ⟨273476386958849267004910007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182317591305899511336606671 273476386958849267004910007)
  ·
    refine ⟨410214580438273900507365011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273476386958849267004910007 410214580438273900507365011)
    ·
      refine ⟨615321870657410850761047517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410214580438273900507365011 615321870657410850761047517)
      ·
        refine ⟨230745701496529069035392819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615321870657410850761047517 230745701496529069035392819)
        ·
          refine ⟨346118552244793603553089229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230745701496529069035392819 346118552244793603553089229)
          ·
            refine ⟨129794457091797601332408461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346118552244793603553089229 129794457091797601332408461)
            ·
              refine ⟨48672921409424100499653173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129794457091797601332408461 48672921409424100499653173)
              ·
                refine ⟨4563086382133509421842485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48672921409424100499653173 4563086382133509421842485)
                ·
                  refine ⟨427789348325016508297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563086382133509421842485 427789348325016508297733)
                  ·
                    rfl

theorem cell23_7498051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 5].length) (baseStart_7498051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498051 prefixEnd_7498051 := by exact prefixLift 7498051
  have htrace : WordTrace (prefixWord ++ tailWord_7498051) baseStart_7498051 baseEnd_7498051 := by
    simpa [prefixWord, tailWord_7498051, baseEnd_7498051] using wordTrace_append hprefix tailTrace_7498051
  have hstable : (prefixWord ++ tailWord_7498051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498051).length < 2 ^ (prefixWord ++ tailWord_7498051).sum := by decide
  have hdescent : baseEnd_7498051 < baseStart_7498051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498068 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 5]
def baseStart_7498068 : Nat := 118140960795 + 7498068 * 2 ^ 59
def prefixEnd_7498068 : Nat := 4983230072969 + 3 ^ 40 * 7498068 * 2
def baseEnd_7498068 : Nat := 427790318232919445351891

theorem tailTrace_7498068 : CollatzResearch.WordTrace tailWord_7498068 prefixEnd_7498068 427790318232919445351891 := by
  unfold tailWord_7498068
  simp only [CollatzResearch.WordTrace]
  refine ⟨136738503499893839454139429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182318004666525119272185905 136738503499893839454139429)
  ·
    refine ⟨25638469406230094897651143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136738503499893839454139429 25638469406230094897651143)
    ·
      refine ⟨38457704109345142346476715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25638469406230094897651143 38457704109345142346476715)
      ·
        refine ⟨57686556164017713519715073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38457704109345142346476715 57686556164017713519715073)
        ·
          refine ⟨43264917123013285139786305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57686556164017713519715073 43264917123013285139786305)
          ·
            refine ⟨32448687842259963854839729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43264917123013285139786305 32448687842259963854839729)
            ·
              refine ⟨24336515881694972891129797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32448687842259963854839729 24336515881694972891129797)
              ·
                refine ⟨4563096727817807417086837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24336515881694972891129797 4563096727817807417086837)
                ·
                  refine ⟨427790318232919445351891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563096727817807417086837 427790318232919445351891)
                  ·
                    rfl

theorem cell23_7498068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_7498068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498068 prefixEnd_7498068 := by exact prefixLift 7498068
  have htrace : WordTrace (prefixWord ++ tailWord_7498068) baseStart_7498068 baseEnd_7498068 := by
    simpa [prefixWord, tailWord_7498068, baseEnd_7498068] using wordTrace_append hprefix tailTrace_7498068
  have hstable : (prefixWord ++ tailWord_7498068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498068).length < 2 ^ (prefixWord ++ tailWord_7498068).sum := by decide
  have hdescent : baseEnd_7498068 < baseStart_7498068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498074 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_7498074 : Nat := 118140960795 + 7498074 * 2 ^ 59
def prefixEnd_7498074 : Nat := 4983230072969 + 3 ^ 40 * 7498074 * 2
def baseEnd_7498074 : Nat := 3850115944980201984691991

theorem tailTrace_7498074 : CollatzResearch.WordTrace tailWord_7498074 prefixEnd_7498074 3850115944980201984691991 := by
  unfold tailWord_7498074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68369306459441485483249319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182318150558510627955331517 68369306459441485483249319)
  ·
    refine ⟨102553959689162228224873979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68369306459441485483249319 102553959689162228224873979)
    ·
      refine ⟨153830939533743342337310969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102553959689162228224873979 153830939533743342337310969)
      ·
        refine ⟨115373204650307506752983227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153830939533743342337310969 115373204650307506752983227)
        ·
          refine ⟨173059806975461260129474841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115373204650307506752983227 173059806975461260129474841)
          ·
            refine ⟨129794855231595945097106131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173059806975461260129474841 129794855231595945097106131)
            ·
              refine ⟨194692282847393917645659197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129794855231595945097106131 194692282847393917645659197)
              ·
                refine ⟨73009606067772719117122199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194692282847393917645659197 73009606067772719117122199)
                ·
                  refine ⟨109514409101659078675683299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73009606067772719117122199 109514409101659078675683299)
                  ·
                    refine ⟨164271613652488618013524949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109514409101659078675683299 164271613652488618013524949)
                    ·
                      refine ⟨3850115944980201984691991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164271613652488618013524949 3850115944980201984691991)
                      ·
                        rfl

theorem cell23_7498074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_7498074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498074 prefixEnd_7498074 := by exact prefixLift 7498074
  have htrace : WordTrace (prefixWord ++ tailWord_7498074) baseStart_7498074 baseEnd_7498074 := by
    simpa [prefixWord, tailWord_7498074, baseEnd_7498074] using wordTrace_append hprefix tailTrace_7498074
  have hstable : (prefixWord ++ tailWord_7498074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498074).length < 2 ^ (prefixWord ++ tailWord_7498074).sum := by decide
  have hdescent : baseEnd_7498074 < baseStart_7498074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498198 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7498198 : Nat := 118140960795 + 7498198 * 2 ^ 59
def prefixEnd_7498198 : Nat := 4983230072969 + 3 ^ 40 * 7498198 * 2
def baseEnd_7498198 : Nat := 3850179616581359499541421

theorem tailTrace_7498198 : CollatzResearch.WordTrace tailWord_7498198 prefixEnd_7498198 3850179616581359499541421 := by
  unfold tailWord_7498198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17092609280582294444406953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182321165659544474073674165 17092609280582294444406953)
  ·
    refine ⟨12819456960436720833305215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17092609280582294444406953 12819456960436720833305215)
    ·
      refine ⟨19229185440655081249957823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12819456960436720833305215 19229185440655081249957823)
      ·
        refine ⟨28843778160982621874936735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19229185440655081249957823 28843778160982621874936735)
        ·
          refine ⟨43265667241473932812405103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28843778160982621874936735 43265667241473932812405103)
          ·
            refine ⟨64898500862210899218607655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43265667241473932812405103 64898500862210899218607655)
            ·
              refine ⟨97347751293316348827911483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64898500862210899218607655 97347751293316348827911483)
              ·
                refine ⟨146021626939974523241867225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97347751293316348827911483 146021626939974523241867225)
                ·
                  refine ⟨109516220204980892431400419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146021626939974523241867225 109516220204980892431400419)
                  ·
                    refine ⟨164274330307471338647100629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109516220204980892431400419 164274330307471338647100629)
                    ·
                      refine ⟨3850179616581359499541421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164274330307471338647100629 3850179616581359499541421)
                      ·
                        rfl

theorem cell23_7498198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7498198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498198 prefixEnd_7498198 := by exact prefixLift 7498198
  have htrace : WordTrace (prefixWord ++ tailWord_7498198) baseStart_7498198 baseEnd_7498198 := by
    simpa [prefixWord, tailWord_7498198, baseEnd_7498198] using wordTrace_append hprefix tailTrace_7498198
  have hstable : (prefixWord ++ tailWord_7498198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498198).length < 2 ^ (prefixWord ++ tailWord_7498198).sum := by decide
  have hdescent : baseEnd_7498198 < baseStart_7498198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498208 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_7498208 : Nat := 118140960795 + 7498208 * 2 ^ 59
def prefixEnd_7498208 : Nat := 4983230072969 + 3 ^ 40 * 7498208 * 2
def baseEnd_7498208 : Nat := 3850184751387904460416375

theorem tailTrace_7498208 : CollatzResearch.WordTrace tailWord_7498208 prefixEnd_7498208 3850184751387904460416375 := by
  unfold tailWord_7498208
  simp only [CollatzResearch.WordTrace]
  refine ⟨136741056609640241409187639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182321408812853655212250185 136741056609640241409187639)
  ·
    refine ⟨205111584914460362113781459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136741056609640241409187639 205111584914460362113781459)
    ·
      refine ⟨307667377371690543170672189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205111584914460362113781459 307667377371690543170672189)
      ·
        refine ⟨115375266514383953689002071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307667377371690543170672189 115375266514383953689002071)
        ·
          refine ⟨173062899771575930533503107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115375266514383953689002071 173062899771575930533503107)
          ·
            refine ⟨259594349657363895800254661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173062899771575930533503107 259594349657363895800254661)
            ·
              refine ⟨48673940560755730462547749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259594349657363895800254661 48673940560755730462547749)
              ·
                refine ⟨9126363855141699461727703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48673940560755730462547749 9126363855141699461727703)
                ·
                  refine ⟨13689545782712549192591555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126363855141699461727703 13689545782712549192591555)
                  ·
                    refine ⟨20534318674068823788887333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13689545782712549192591555 20534318674068823788887333)
                    ·
                      refine ⟨3850184751387904460416375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20534318674068823788887333 3850184751387904460416375)
                      ·
                        rfl

theorem cell23_7498208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_7498208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498208 prefixEnd_7498208 := by exact prefixLift 7498208
  have htrace : WordTrace (prefixWord ++ tailWord_7498208) baseStart_7498208 baseEnd_7498208 := by
    simpa [prefixWord, tailWord_7498208, baseEnd_7498208] using wordTrace_append hprefix tailTrace_7498208
  have hstable : (prefixWord ++ tailWord_7498208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498208).length < 2 ^ (prefixWord ++ tailWord_7498208).sum := by decide
  have hdescent : baseEnd_7498208 < baseStart_7498208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498218 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_7498218 : Nat := 118140960795 + 7498218 * 2 ^ 59
def prefixEnd_7498218 : Nat := 4983230072969 + 3 ^ 40 * 7498218 * 2
def baseEnd_7498218 : Nat := 1283396628731483140430443

theorem tailTrace_7498218 : CollatzResearch.WordTrace tailWord_7498218 prefixEnd_7498218 1283396628731483140430443 := by
  unfold tailWord_7498218
  simp only [CollatzResearch.WordTrace]
  refine ⟨68370619487311063631559827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182321651966162836350826205 68370619487311063631559827)
  ·
    refine ⟨102555929230966595447339741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68370619487311063631559827 102555929230966595447339741)
    ·
      refine ⟨38458473461612473292752403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102555929230966595447339741 38458473461612473292752403)
      ·
        refine ⟨57687710192418709939128605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38458473461612473292752403 57687710192418709939128605)
        ·
          refine ⟨21632891322157016227173227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57687710192418709939128605 21632891322157016227173227)
          ·
            refine ⟨32449336983235524340759841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21632891322157016227173227 32449336983235524340759841)
            ·
              refine ⟨24337002737426643255569881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32449336983235524340759841 24337002737426643255569881)
              ·
                refine ⟨18252752053069982441677411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24337002737426643255569881 18252752053069982441677411)
                ·
                  refine ⟨27379128079604973662516117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18252752053069982441677411 27379128079604973662516117)
                  ·
                    refine ⟨1283396628731483140430443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27379128079604973662516117 1283396628731483140430443)
                    ·
                      rfl

theorem cell23_7498218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_7498218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498218 prefixEnd_7498218 := by exact prefixLift 7498218
  have htrace : WordTrace (prefixWord ++ tailWord_7498218) baseStart_7498218 baseEnd_7498218 := by
    simpa [prefixWord, tailWord_7498218, baseEnd_7498218] using wordTrace_append hprefix tailTrace_7498218
  have hstable : (prefixWord ++ tailWord_7498218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498218).length < 2 ^ (prefixWord ++ tailWord_7498218).sum := by decide
  have hdescent : baseEnd_7498218 < baseStart_7498218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498222 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7498222 : Nat := 118140960795 + 7498222 * 2 ^ 59
def prefixEnd_7498222 : Nat := 4983230072969 + 3 ^ 40 * 7498222 * 2
def baseEnd_7498222 : Nat := 1283397313372355801880437

theorem tailTrace_7498222 : CollatzResearch.WordTrace tailWord_7498222 prefixEnd_7498222 1283397313372355801880437 := by
  unfold tailWord_7498222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34185327980153720401173115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182321749227486508806256613 34185327980153720401173115)
  ·
    refine ⟨51277991970230580601759673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34185327980153720401173115 51277991970230580601759673)
    ·
      refine ⟨38458493977672935451319755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51277991970230580601759673 38458493977672935451319755)
      ·
        refine ⟨57687740966509403176979633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38458493977672935451319755 57687740966509403176979633)
        ·
          refine ⟨43265805724882052382734725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57687740966509403176979633 43265805724882052382734725)
          ·
            refine ⟨8112338573415384821762761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43265805724882052382734725 8112338573415384821762761)
            ·
              refine ⟨6084253930061538616322071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112338573415384821762761 6084253930061538616322071)
              ·
                refine ⟨9126380895092307924483107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084253930061538616322071 9126380895092307924483107)
                ·
                  refine ⟨13689571342638461886724661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126380895092307924483107 13689571342638461886724661)
                  ·
                    refine ⟨1283397313372355801880437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13689571342638461886724661 1283397313372355801880437)
                    ·
                      rfl

theorem cell23_7498222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7498222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498222 prefixEnd_7498222 := by exact prefixLift 7498222
  have htrace : WordTrace (prefixWord ++ tailWord_7498222) baseStart_7498222 baseEnd_7498222 := by
    simpa [prefixWord, tailWord_7498222, baseEnd_7498222] using wordTrace_append hprefix tailTrace_7498222
  have hstable : (prefixWord ++ tailWord_7498222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498222).length < 2 ^ (prefixWord ++ tailWord_7498222).sum := by decide
  have hdescent : baseEnd_7498222 < baseStart_7498222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498225 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_7498225 : Nat := 118140960795 + 7498225 * 2 ^ 59
def prefixEnd_7498225 : Nat := 4983230072969 + 3 ^ 40 * 7498225 * 2
def baseEnd_7498225 : Nat := 3850193480559030893903797

theorem tailTrace_7498225 : CollatzResearch.WordTrace tailWord_7498225 prefixEnd_7498225 3850193480559030893903797 := by
  unfold tailWord_7498225
  simp only [CollatzResearch.WordTrace]
  refine ⟨273482733260218894721744129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182321822173479263147829419 273482733260218894721744129)
  ·
    refine ⟨205112049945164171041308097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273482733260218894721744129 205112049945164171041308097)
    ·
      refine ⟨153834037458873128280981073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205112049945164171041308097 153834037458873128280981073)
      ·
        refine ⟨115375528094154846210735805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153834037458873128280981073 115375528094154846210735805)
        ·
          refine ⟨43265823035308067329025927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115375528094154846210735805 43265823035308067329025927)
          ·
            refine ⟨64898734552962100993538891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43265823035308067329025927 64898734552962100993538891)
            ·
              refine ⟨97348101829443151490308337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64898734552962100993538891 97348101829443151490308337)
              ·
                refine ⟨73011076372082363617731253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97348101829443151490308337 73011076372082363617731253)
                ·
                  refine ⟨6844788409882721589162305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73011076372082363617731253 6844788409882721589162305)
                  ·
                    refine ⟨5133591307412041191871729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844788409882721589162305 5133591307412041191871729)
                    ·
                      refine ⟨3850193480559030893903797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133591307412041191871729 3850193480559030893903797)
                      ·
                        rfl

theorem cell23_7498225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_7498225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498225 prefixEnd_7498225 := by exact prefixLift 7498225
  have htrace : WordTrace (prefixWord ++ tailWord_7498225) baseStart_7498225 baseEnd_7498225 := by
    simpa [prefixWord, tailWord_7498225, baseEnd_7498225] using wordTrace_append hprefix tailTrace_7498225
  have hstable : (prefixWord ++ tailWord_7498225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498225).length < 2 ^ (prefixWord ++ tailWord_7498225).sum := by decide
  have hdescent : baseEnd_7498225 < baseStart_7498225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498252 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_7498252 : Nat := 118140960795 + 7498252 * 2 ^ 59
def prefixEnd_7498252 : Nat := 4983230072969 + 3 ^ 40 * 7498252 * 2
def baseEnd_7498252 : Nat := 1283402448178900762755391

theorem tailTrace_7498252 : CollatzResearch.WordTrace tailWord_7498252 prefixEnd_7498252 1283402448178900762755391 := by
  unfold tailWord_7498252
  simp only [CollatzResearch.WordTrace]
  refine ⟨136741859015560539166488505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182322478687414052221984673 136741859015560539166488505)
  ·
    refine ⟨102556394261670404374866379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136741859015560539166488505 102556394261670404374866379)
    ·
      refine ⟨153834591392505606562299569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102556394261670404374866379 153834591392505606562299569)
      ·
        refine ⟨115375943544379204921724677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153834591392505606562299569 115375943544379204921724677)
        ·
          refine ⟨21632989414571100922823377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115375943544379204921724677 21632989414571100922823377)
          ·
            refine ⟨16224742060928325692117533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21632989414571100922823377 16224742060928325692117533)
            ·
              refine ⟨6084278272848122134544075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16224742060928325692117533 6084278272848122134544075)
              ·
                refine ⟨9126417409272183201816113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084278272848122134544075 9126417409272183201816113)
                ·
                  refine ⟨6844813056954137401362085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126417409272183201816113 6844813056954137401362085)
                  ·
                    refine ⟨1283402448178900762755391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844813056954137401362085 1283402448178900762755391)
                    ·
                      rfl

theorem cell23_7498252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_7498252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498252 prefixEnd_7498252 := by exact prefixLift 7498252
  have htrace : WordTrace (prefixWord ++ tailWord_7498252) baseStart_7498252 baseEnd_7498252 := by
    simpa [prefixWord, tailWord_7498252, baseEnd_7498252] using wordTrace_append hprefix tailTrace_7498252
  have hstable : (prefixWord ++ tailWord_7498252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498252).length < 2 ^ (prefixWord ++ tailWord_7498252).sum := by decide
  have hdescent : baseEnd_7498252 < baseStart_7498252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498275 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 3]
def baseStart_7498275 : Nat := 118140960795 + 7498275 * 2 ^ 59
def prefixEnd_7498275 : Nat := 4983230072969 + 3 ^ 40 * 7498275 * 2
def baseEnd_7498275 : Nat := 3850219154591755698278567

theorem tailTrace_7498275 : CollatzResearch.WordTrace tailWord_7498275 prefixEnd_7498275 3850219154591755698278567 := by
  unfold tailWord_7498275
  simp only [CollatzResearch.WordTrace]
  refine ⟨273484556910037753261064279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182323037940025168840709519 273484556910037753261064279)
  ·
    refine ⟨410226835365056629891596419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273484556910037753261064279 410226835365056629891596419)
    ·
      refine ⟨615340253047584944837394629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410226835365056629891596419 615340253047584944837394629)
      ·
        refine ⟨115376297446422177157011493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615340253047584944837394629 115376297446422177157011493)
        ·
          refine ⟨21633055771204158216939655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115376297446422177157011493 21633055771204158216939655)
          ·
            refine ⟨32449583656806237325409483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21633055771204158216939655 32449583656806237325409483)
            ·
              refine ⟨48674375485209355988114225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32449583656806237325409483 48674375485209355988114225)
              ·
                refine ⟨36505781613907016991085669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48674375485209355988114225 36505781613907016991085669)
                ·
                  refine ⟨6844834052607565685828563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36505781613907016991085669 6844834052607565685828563)
                  ·
                    refine ⟨10267251078911348528742845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6844834052607565685828563 10267251078911348528742845)
                    ·
                      refine ⟨3850219154591755698278567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10267251078911348528742845 3850219154591755698278567)
                      ·
                        rfl

theorem cell23_7498275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_7498275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498275 prefixEnd_7498275 := by exact prefixLift 7498275
  have htrace : WordTrace (prefixWord ++ tailWord_7498275) baseStart_7498275 baseEnd_7498275 := by
    simpa [prefixWord, tailWord_7498275, baseEnd_7498275] using wordTrace_append hprefix tailTrace_7498275
  have hstable : (prefixWord ++ tailWord_7498275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498275).length < 2 ^ (prefixWord ++ tailWord_7498275).sum := by decide
  have hdescent : baseEnd_7498275 < baseStart_7498275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498309 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_7498309 : Nat := 118140960795 + 7498309 * 2 ^ 59
def prefixEnd_7498309 : Nat := 4983230072969 + 3 ^ 40 * 7498309 * 2
def baseEnd_7498309 : Nat := 3850236612934008565253411

theorem tailTrace_7498309 : CollatzResearch.WordTrace tailWord_7498309 prefixEnd_7498309 3850236612934008565253411 := by
  unfold tailWord_7498309
  simp only [CollatzResearch.WordTrace]
  refine ⟨273485796991914577067801981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182323864661276384711867987 273485796991914577067801981)
  ·
    refine ⟨102557173871967966400425743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273485796991914577067801981 102557173871967966400425743)
    ·
      refine ⟨153835760807951949600638615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102557173871967966400425743 153835760807951949600638615)
      ·
        refine ⟨230753641211927924400957923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153835760807951949600638615 230753641211927924400957923)
        ·
          refine ⟨346130461817891886601436885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230753641211927924400957923 346130461817891886601436885)
          ·
            refine ⟨8112432698856841092221177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346130461817891886601436885 8112432698856841092221177)
            ·
              refine ⟨6084324524142630819165883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112432698856841092221177 6084324524142630819165883)
              ·
                refine ⟨9126486786213946228748825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084324524142630819165883 9126486786213946228748825)
                ·
                  refine ⟨6844865089660459671561619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126486786213946228748825 6844865089660459671561619)
                  ·
                    refine ⟨10267297634490689507342429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6844865089660459671561619 10267297634490689507342429)
                    ·
                      refine ⟨3850236612934008565253411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10267297634490689507342429 3850236612934008565253411)
                      ·
                        rfl

theorem cell23_7498309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_7498309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498309 prefixEnd_7498309 := by exact prefixLift 7498309
  have htrace : WordTrace (prefixWord ++ tailWord_7498309) baseStart_7498309 baseEnd_7498309 := by
    simpa [prefixWord, tailWord_7498309, baseEnd_7498309] using wordTrace_append hprefix tailTrace_7498309
  have hstable : (prefixWord ++ tailWord_7498309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498309).length < 2 ^ (prefixWord ++ tailWord_7498309).sum := by decide
  have hdescent : baseEnd_7498309 < baseStart_7498309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498318 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7498318 : Nat := 118140960795 + 7498318 * 2 ^ 59
def prefixEnd_7498318 : Nat := 4983230072969 + 3 ^ 40 * 7498318 * 2
def baseEnd_7498318 : Nat := 3850241234259899030040869

theorem tailTrace_7498318 : CollatzResearch.WordTrace tailWord_7498318 prefixEnd_7498318 3850241234259899030040869 := by
  unfold tailWord_7498318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34185765656110246450609951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182324083499254647736586405 34185765656110246450609951)
  ·
    refine ⟨51278648484165369675914927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34185765656110246450609951 51278648484165369675914927)
    ·
      refine ⟨76917972726248054513872391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51278648484165369675914927 76917972726248054513872391)
      ·
        refine ⟨115376959089372081770808587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76917972726248054513872391 115376959089372081770808587)
        ·
          refine ⟨173065438634058122656212881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115376959089372081770808587 173065438634058122656212881)
          ·
            refine ⟨129799078975543591992159661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173065438634058122656212881 129799078975543591992159661)
            ·
              refine ⟨48674654615828846997059873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129799078975543591992159661 48674654615828846997059873)
              ·
                refine ⟨36505990961871635247794905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48674654615828846997059873 36505990961871635247794905)
                ·
                  refine ⟨27379493221403726435846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36505990961871635247794905 27379493221403726435846179)
                  ·
                    refine ⟨41069239832105589653769269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27379493221403726435846179 41069239832105589653769269)
                    ·
                      refine ⟨3850241234259899030040869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41069239832105589653769269 3850241234259899030040869)
                      ·
                        rfl

theorem cell23_7498318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7498318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498318 prefixEnd_7498318 := by exact prefixLift 7498318
  have htrace : WordTrace (prefixWord ++ tailWord_7498318) baseStart_7498318 baseEnd_7498318 := by
    simpa [prefixWord, tailWord_7498318, baseEnd_7498318] using wordTrace_append hprefix tailTrace_7498318
  have hstable : (prefixWord ++ tailWord_7498318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498318).length < 2 ^ (prefixWord ++ tailWord_7498318).sum := by decide
  have hdescent : baseEnd_7498318 < baseStart_7498318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498349 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7498349 : Nat := 118140960795 + 7498349 * 2 ^ 59
def prefixEnd_7498349 : Nat := 4983230072969 + 3 ^ 40 * 7498349 * 2
def baseEnd_7498349 : Nat := 3850257152160188408753227

theorem tailTrace_7498349 : CollatzResearch.WordTrace tailWord_7498349 prefixEnd_7498349 3850257152160188408753227 := by
  unfold tailWord_7498349
  simp only [CollatzResearch.WordTrace]
  refine ⟨273487255911769663899258101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182324837274513109266172067 273487255911769663899258101)
  ·
    refine ⟨25639430241728405990555447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273487255911769663899258101 25639430241728405990555447)
    ·
      refine ⟨38459145362592608985833171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25639430241728405990555447 38459145362592608985833171)
      ·
        refine ⟨57688718043888913478749757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38459145362592608985833171 57688718043888913478749757)
        ·
          refine ⟨21633269266458342554531159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57688718043888913478749757 21633269266458342554531159)
          ·
            refine ⟨32449903899687513831796739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21633269266458342554531159 32449903899687513831796739)
            ·
              refine ⟨48674855849531270747695109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32449903899687513831796739 48674855849531270747695109)
              ·
                refine ⟨9126535471787113265192833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48674855849531270747695109 9126535471787113265192833)
                ·
                  refine ⟨6844901603840334948894625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126535471787113265192833 6844901603840334948894625)
                  ·
                    refine ⟨5133676202880251211670969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6844901603840334948894625 5133676202880251211670969)
                    ·
                      refine ⟨3850257152160188408753227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133676202880251211670969 3850257152160188408753227)
                      ·
                        rfl

theorem cell23_7498349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7498349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498349 prefixEnd_7498349 := by exact prefixLift 7498349
  have htrace : WordTrace (prefixWord ++ tailWord_7498349) baseStart_7498349 baseEnd_7498349 := by
    simpa [prefixWord, tailWord_7498349, baseEnd_7498349] using wordTrace_append hprefix tailTrace_7498349
  have hstable : (prefixWord ++ tailWord_7498349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498349).length < 2 ^ (prefixWord ++ tailWord_7498349).sum := by decide
  have hdescent : baseEnd_7498349 < baseStart_7498349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498375 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_7498375 : Nat := 118140960795 + 7498375 * 2 ^ 59
def prefixEnd_7498375 : Nat := 4983230072969 + 3 ^ 40 * 7498375 * 2
def baseEnd_7498375 : Nat := 3850270502657205307028107

theorem tailTrace_7498375 : CollatzResearch.WordTrace tailWord_7498375 prefixEnd_7498375 3850270502657205307028107 := by
  unfold tailWord_7498375
  simp only [CollatzResearch.WordTrace]
  refine ⟨273488204209675470339704579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182325469473116980226469719 273488204209675470339704579)
  ·
    refine ⟨410232306314513205509556869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273488204209675470339704579 410232306314513205509556869)
    ·
      refine ⟨76918557433971226033041913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410232306314513205509556869 76918557433971226033041913)
      ·
        refine ⟨57688918075478419524781435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76918557433971226033041913 57688918075478419524781435)
        ·
          refine ⟨86533377113217629287172153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57688918075478419524781435 86533377113217629287172153)
          ·
            refine ⟨64900032834913221965379115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86533377113217629287172153 64900032834913221965379115)
            ·
              refine ⟨97350049252369832948068673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64900032834913221965379115 97350049252369832948068673)
              ·
                refine ⟨73012536939277374711051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97350049252369832948068673 73012536939277374711051505)
                ·
                  refine ⟨54759402704458031033288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73012536939277374711051505 54759402704458031033288629)
                  ·
                    refine ⟨5133694003542940409370809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54759402704458031033288629 5133694003542940409370809)
                    ·
                      refine ⟨3850270502657205307028107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133694003542940409370809 3850270502657205307028107)
                      ·
                        rfl

theorem cell23_7498375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_7498375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498375 prefixEnd_7498375 := by exact prefixLift 7498375
  have htrace : WordTrace (prefixWord ++ tailWord_7498375) baseStart_7498375 baseEnd_7498375 := by
    simpa [prefixWord, tailWord_7498375, baseEnd_7498375] using wordTrace_append hprefix tailTrace_7498375
  have hstable : (prefixWord ++ tailWord_7498375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498375).length < 2 ^ (prefixWord ++ tailWord_7498375).sum := by decide
  have hdescent : baseEnd_7498375 < baseStart_7498375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498415 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 3, 4]
def baseStart_7498415 : Nat := 118140960795 + 7498415 * 2 ^ 59
def prefixEnd_7498415 : Nat := 4983230072969 + 3 ^ 40 * 7498415 * 2
def baseEnd_7498415 : Nat := 1283430347294461716842641

theorem tailTrace_7498415 : CollatzResearch.WordTrace tailWord_7498415 prefixEnd_7498415 1283430347294461716842641 := by
  unfold tailWord_7498415
  simp only [CollatzResearch.WordTrace]
  refine ⟨273489663129530557171160699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182326442086353704780773799 273489663129530557171160699)
  ·
    refine ⟨410234494694295835756741049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273489663129530557171160699 410234494694295835756741049)
    ·
      refine ⟨307675871020721876817555787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410234494694295835756741049 307675871020721876817555787)
      ·
        refine ⟨461513806531082815226333681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307675871020721876817555787 461513806531082815226333681)
        ·
          refine ⟨346135354898312111419750261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461513806531082815226333681 346135354898312111419750261)
          ·
            refine ⟨32450189521716760445601587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346135354898312111419750261 32450189521716760445601587)
            ·
              refine ⟨48675284282575140668402381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32450189521716760445601587 48675284282575140668402381)
              ·
                refine ⟨18253231605965677750650893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48675284282575140668402381 18253231605965677750650893)
                ·
                  refine ⟨6844961852237129156494085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18253231605965677750650893 6844961852237129156494085)
                  ·
                    refine ⟨1283430347294461716842641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6844961852237129156494085 1283430347294461716842641)
                    ·
                      rfl

theorem cell23_7498415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_7498415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498415 prefixEnd_7498415 := by exact prefixLift 7498415
  have htrace : WordTrace (prefixWord ++ tailWord_7498415) baseStart_7498415 baseEnd_7498415 := by
    simpa [prefixWord, tailWord_7498415, baseEnd_7498415] using wordTrace_append hprefix tailTrace_7498415
  have hstable : (prefixWord ++ tailWord_7498415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498415).length < 2 ^ (prefixWord ++ tailWord_7498415).sum := by decide
  have hdescent : baseEnd_7498415 < baseStart_7498415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498418 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_7498418 : Nat := 118140960795 + 7498418 * 2 ^ 59
def prefixEnd_7498418 : Nat := 4983230072969 + 3 ^ 40 * 7498418 * 2
def baseEnd_7498418 : Nat := 3850292582325348638790409

theorem tailTrace_7498418 : CollatzResearch.WordTrace tailWord_7498418 prefixEnd_7498418 3850292582325348638790409 := by
  unfold tailWord_7498418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68372443137129922170879977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182326515032346459122346605 68372443137129922170879977)
  ·
    refine ⟨51279332352847441628159983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68372443137129922170879977 51279332352847441628159983)
    ·
      refine ⟨76918998529271162442239975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51279332352847441628159983 76918998529271162442239975)
      ·
        refine ⟨115378497793906743663359963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76918998529271162442239975 115378497793906743663359963)
        ·
          refine ⟨173067746690860115495039945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115378497793906743663359963 173067746690860115495039945)
          ·
            refine ⟨129800810018145086621279959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173067746690860115495039945 129800810018145086621279959)
            ·
              refine ⟨194701215027217629931919939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129800810018145086621279959 194701215027217629931919939)
              ·
                refine ⟨292051822540826444897879909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194701215027217629931919939 292051822540826444897879909)
                ·
                  refine ⟨54759716726404958418352483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292051822540826444897879909 54759716726404958418352483)
                  ·
                    refine ⟨82139575089607437627528725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54759716726404958418352483 82139575089607437627528725)
                    ·
                      refine ⟨3850292582325348638790409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82139575089607437627528725 3850292582325348638790409)
                      ·
                        rfl

theorem cell23_7498418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_7498418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498418 prefixEnd_7498418 := by exact prefixLift 7498418
  have htrace : WordTrace (prefixWord ++ tailWord_7498418) baseStart_7498418 baseEnd_7498418 := by
    simpa [prefixWord, tailWord_7498418, baseEnd_7498418] using wordTrace_append hprefix tailTrace_7498418
  have hstable : (prefixWord ++ tailWord_7498418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498418).length < 2 ^ (prefixWord ++ tailWord_7498418).sum := by decide
  have hdescent : baseEnd_7498418 < baseStart_7498418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498492 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_7498492 : Nat := 118140960795 + 7498492 * 2 ^ 59
def prefixEnd_7498492 : Nat := 4983230072969 + 3 ^ 40 * 7498492 * 2
def baseEnd_7498492 : Nat := 1283443526631260449755023

theorem tailTrace_7498492 : CollatzResearch.WordTrace tailWord_7498492 prefixEnd_7498492 1283443526631260449755023 := by
  unfold tailWord_7498492
  simp only [CollatzResearch.WordTrace]
  refine ⟨136746235775125799660856865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182328314366834399547809153 136746235775125799660856865)
  ·
    refine ⟨102559676831344349745642649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136746235775125799660856865 102559676831344349745642649)
    ·
      refine ⟨76919757623508262309231987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102559676831344349745642649 76919757623508262309231987)
      ·
        refine ⟨115379636435262393463847981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76919757623508262309231987 115379636435262393463847981)
        ·
          refine ⟨43267363663223397548942993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115379636435262393463847981 43267363663223397548942993)
          ·
            refine ⟨32450522747417548161707245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43267363663223397548942993 32450522747417548161707245)
            ·
              refine ⟨12168946030281580560640217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32450522747417548161707245 12168946030281580560640217)
              ·
                refine ⟨9126709522711185420480163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12168946030281580560640217 9126709522711185420480163)
                ·
                  refine ⟨13690064284066778130720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9126709522711185420480163 13690064284066778130720245)
                  ·
                    refine ⟨1283443526631260449755023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13690064284066778130720245 1283443526631260449755023)
                    ·
                      rfl

theorem cell23_7498492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_7498492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498492 prefixEnd_7498492 := by exact prefixLift 7498492
  have htrace : WordTrace (prefixWord ++ tailWord_7498492) baseStart_7498492 baseEnd_7498492 := by
    simpa [prefixWord, tailWord_7498492, baseEnd_7498492] using wordTrace_append hprefix tailTrace_7498492
  have hstable : (prefixWord ++ tailWord_7498492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498492).length < 2 ^ (prefixWord ++ tailWord_7498492).sum := by decide
  have hdescent : baseEnd_7498492 < baseStart_7498492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498505 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_7498505 : Nat := 118140960795 + 7498505 * 2 ^ 59
def prefixEnd_7498505 : Nat := 4983230072969 + 3 ^ 40 * 7498505 * 2
def baseEnd_7498505 : Nat := 1283445751714096599467503

theorem tailTrace_7498505 : CollatzResearch.WordTrace tailWord_7498505 prefixEnd_7498505 1283445751714096599467503 := by
  unfold tailWord_7498505
  simp only [CollatzResearch.WordTrace]
  refine ⟨273492945699204502541936969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182328630466136335027957979 273492945699204502541936969)
  ·
    refine ⟨205119709274403376906452727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273492945699204502541936969 205119709274403376906452727)
    ·
      refine ⟨307679563911605065359679091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205119709274403376906452727 307679563911605065359679091)
      ·
        refine ⟨461519345867407598039518637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307679563911605065359679091 461519345867407598039518637)
        ·
          refine ⟨173069754700277849264819489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461519345867407598039518637 173069754700277849264819489)
          ·
            refine ⟨129802316025208386948614617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173069754700277849264819489 129802316025208386948614617)
            ·
              refine ⟨97351737018906290211460963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129802316025208386948614617 97351737018906290211460963)
              ·
                refine ⟨146027605528359435317191445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97351737018906290211460963 146027605528359435317191445)
                ·
                  refine ⟨6845044009141848530493349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146027605528359435317191445 6845044009141848530493349)
                  ·
                    refine ⟨1283445751714096599467503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845044009141848530493349 1283445751714096599467503)
                    ·
                      rfl

theorem cell23_7498505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_7498505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498505 prefixEnd_7498505 := by exact prefixLift 7498505
  have htrace : WordTrace (prefixWord ++ tailWord_7498505) baseStart_7498505 baseEnd_7498505 := by
    simpa [prefixWord, tailWord_7498505, baseEnd_7498505] using wordTrace_append hprefix tailTrace_7498505
  have hstable : (prefixWord ++ tailWord_7498505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498505).length < 2 ^ (prefixWord ++ tailWord_7498505).sum := by decide
  have hdescent : baseEnd_7498505 < baseStart_7498505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498529 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7498529 : Nat := 118140960795 + 7498529 * 2 ^ 59
def prefixEnd_7498529 : Nat := 4983230072969 + 3 ^ 40 * 7498529 * 2
def baseEnd_7498529 : Nat := 3850349578677997704502399

theorem tailTrace_7498529 : CollatzResearch.WordTrace tailWord_7498529 prefixEnd_7498529 3850349578677997704502399 := by
  unfold tailWord_7498529
  simp only [CollatzResearch.WordTrace]
  refine ⟨273493821051117554640810641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182329214034078369760540427 273493821051117554640810641)
  ·
    refine ⟨205120365788338165980607981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273493821051117554640810641 205120365788338165980607981)
    ·
      refine ⟨76920137170626812242727993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205120365788338165980607981 76920137170626812242727993)
      ·
        refine ⟨57690102877970109182045995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76920137170626812242727993 57690102877970109182045995)
        ·
          refine ⟨86535154316955163773068993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57690102877970109182045995 86535154316955163773068993)
          ·
            refine ⟨64901365737716372829801745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86535154316955163773068993 64901365737716372829801745)
            ·
              refine ⟨48676024303287279622351309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64901365737716372829801745 48676024303287279622351309)
              ·
                refine ⟨18253509113732729858381741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48676024303287279622351309 18253509113732729858381741)
                ·
                  refine ⟨6845065917649773696893153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18253509113732729858381741 6845065917649773696893153)
                  ·
                    refine ⟨5133799438237330272669865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6845065917649773696893153 5133799438237330272669865)
                    ·
                      refine ⟨3850349578677997704502399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133799438237330272669865 3850349578677997704502399)
                      ·
                        rfl

theorem cell23_7498529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7498529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498529 prefixEnd_7498529 := by exact prefixLift 7498529
  have htrace : WordTrace (prefixWord ++ tailWord_7498529) baseStart_7498529 baseEnd_7498529 := by
    simpa [prefixWord, tailWord_7498529, baseEnd_7498529] using wordTrace_append hprefix tailTrace_7498529
  have hstable : (prefixWord ++ tailWord_7498529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498529).length < 2 ^ (prefixWord ++ tailWord_7498529).sum := by decide
  have hdescent : baseEnd_7498529 < baseStart_7498529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498550 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7498550 : Nat := 118140960795 + 7498550 * 2 ^ 59
def prefixEnd_7498550 : Nat := 4983230072969 + 3 ^ 40 * 7498550 * 2
def baseEnd_7498550 : Nat := 3850360361771742122339803

theorem tailTrace_7498550 : CollatzResearch.WordTrace tailWord_7498550 prefixEnd_7498550 3850360361771742122339803 := by
  unfold tailWord_7498550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093411686502592201707819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182329724656027650151550069 17093411686502592201707819)
  ·
    refine ⟨25640117529753888302561729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17093411686502592201707819 25640117529753888302561729)
    ·
      refine ⟨19230088147315416226921297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25640117529753888302561729 19230088147315416226921297)
      ·
        refine ⟨14422566110486562170190973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19230088147315416226921297 14422566110486562170190973)
        ·
          refine ⟨5408462291432460813821615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14422566110486562170190973 5408462291432460813821615)
          ·
            refine ⟨8112693437148691220732423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408462291432460813821615 8112693437148691220732423)
            ·
              refine ⟨12169040155723036831098635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112693437148691220732423 12169040155723036831098635)
              ·
                refine ⟨18253560233584555246647953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169040155723036831098635 18253560233584555246647953)
                ·
                  refine ⟨13690170175188416434985965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18253560233584555246647953 13690170175188416434985965)
                  ·
                    refine ⟨5133813815695656163119737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13690170175188416434985965 5133813815695656163119737)
                    ·
                      refine ⟨3850360361771742122339803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133813815695656163119737 3850360361771742122339803)
                      ·
                        rfl

theorem cell23_7498550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7498550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498550 prefixEnd_7498550 := by exact prefixLift 7498550
  have htrace : WordTrace (prefixWord ++ tailWord_7498550) baseStart_7498550 baseEnd_7498550 := by
    simpa [prefixWord, tailWord_7498550, baseEnd_7498550] using wordTrace_append hprefix tailTrace_7498550
  have hstable : (prefixWord ++ tailWord_7498550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498550).length < 2 ^ (prefixWord ++ tailWord_7498550).sum := by decide
  have hdescent : baseEnd_7498550 < baseStart_7498550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498573 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7498573 : Nat := 118140960795 + 7498573 * 2 ^ 59
def prefixEnd_7498573 : Nat := 4983230072969 + 3 ^ 40 * 7498573 * 2
def baseEnd_7498573 : Nat := 1283457390608931844117399

theorem tailTrace_7498573 : CollatzResearch.WordTrace tailWord_7498573 prefixEnd_7498573 1283457390608931844117399 := by
  unfold tailWord_7498573
  simp only [CollatzResearch.WordTrace]
  refine ⟨273495425862958150155412373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182330283908638766770274915 273495425862958150155412373)
  ·
    refine ⟨12820098087326163288534955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273495425862958150155412373 12820098087326163288534955)
    ·
      refine ⟨19230147130989244932802433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12820098087326163288534955 19230147130989244932802433)
      ·
        refine ⟨14422610348241933699601825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19230147130989244932802433 14422610348241933699601825)
        ·
          refine ⟨10816957761181450274701369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14422610348241933699601825 10816957761181450274701369)
          ·
            refine ⟨8112718320886087706026027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10816957761181450274701369 8112718320886087706026027)
            ·
              refine ⟨12169077481329131559039041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8112718320886087706026027 12169077481329131559039041)
              ·
                refine ⟨9126808110996848669279281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12169077481329131559039041 9126808110996848669279281)
                ·
                  refine ⟨6845106083247636501959461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9126808110996848669279281 6845106083247636501959461)
                  ·
                    refine ⟨1283457390608931844117399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845106083247636501959461 1283457390608931844117399)
                    ·
                      rfl

theorem cell23_7498573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7498573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498573 prefixEnd_7498573 := by exact prefixLift 7498573
  have htrace : WordTrace (prefixWord ++ tailWord_7498573) baseStart_7498573 baseEnd_7498573 := by
    simpa [prefixWord, tailWord_7498573, baseEnd_7498573] using wordTrace_append hprefix tailTrace_7498573
  have hstable : (prefixWord ++ tailWord_7498573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498573).length < 2 ^ (prefixWord ++ tailWord_7498573).sum := by decide
  have hdescent : baseEnd_7498573 < baseStart_7498573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498615 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_7498615 : Nat := 118140960795 + 7498615 * 2 ^ 59
def prefixEnd_7498615 : Nat := 4983230072969 + 3 ^ 40 * 7498615 * 2
def baseEnd_7498615 : Nat := 3850393738014284368027003

theorem tailTrace_7498615 : CollatzResearch.WordTrace tailWord_7498615 prefixEnd_7498615 3850393738014284368027003 := by
  unfold tailWord_7498615
  simp only [CollatzResearch.WordTrace]
  refine ⟨273496957728805991328441299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182331305152537327552294199 273496957728805991328441299)
  ·
    refine ⟨410245436593208986992661949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273496957728805991328441299 410245436593208986992661949)
    ·
      refine ⟨153842038722453370122248231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410245436593208986992661949 153842038722453370122248231)
      ·
        refine ⟨230763058083680055183372347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153842038722453370122248231 230763058083680055183372347)
        ·
          refine ⟨346144587125520082775058521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230763058083680055183372347 346144587125520082775058521)
          ·
            refine ⟨259608440344140062081293891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346144587125520082775058521 259608440344140062081293891)
            ·
              refine ⟨389412660516210093121940837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259608440344140062081293891 389412660516210093121940837)
              ·
                refine ⟨73014873846789392460363907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389412660516210093121940837 73014873846789392460363907)
                ·
                  refine ⟨109522310770184088690545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73014873846789392460363907 109522310770184088690545861)
                  ·
                    refine ⟨20535433269409516629477349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109522310770184088690545861 20535433269409516629477349)
                    ·
                      refine ⟨3850393738014284368027003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20535433269409516629477349 3850393738014284368027003)
                      ·
                        rfl

theorem cell23_7498615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_7498615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498615 prefixEnd_7498615 := by exact prefixLift 7498615
  have htrace : WordTrace (prefixWord ++ tailWord_7498615) baseStart_7498615 baseEnd_7498615 := by
    simpa [prefixWord, tailWord_7498615, baseEnd_7498615] using wordTrace_append hprefix tailTrace_7498615
  have hstable : (prefixWord ++ tailWord_7498615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498615).length < 2 ^ (prefixWord ++ tailWord_7498615).sum := by decide
  have hdescent : baseEnd_7498615 < baseStart_7498615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498619 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 4, 2, 2]
def baseStart_7498619 : Nat := 118140960795 + 7498619 * 2 ^ 59
def prefixEnd_7498619 : Nat := 4983230072969 + 3 ^ 40 * 7498619 * 2
def baseEnd_7498619 : Nat := 3850395791936902352376985

theorem tailTrace_7498619 : CollatzResearch.WordTrace tailWord_7498619 prefixEnd_7498619 3850395791936902352376985 := by
  unfold tailWord_7498619
  simp only [CollatzResearch.WordTrace]
  refine ⟨273497103620791500011586911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182331402413861000007724607 273497103620791500011586911)
  ·
    refine ⟨410245655431187250017380367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273497103620791500011586911 410245655431187250017380367)
    ·
      refine ⟨615368483146780875026070551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410245655431187250017380367 615368483146780875026070551)
      ·
        refine ⟨923052724720171312539105827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615368483146780875026070551 923052724720171312539105827)
        ·
          refine ⟨1384579087080256968808658741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923052724720171312539105827 1384579087080256968808658741)
          ·
            refine ⟨129804289413774090825811757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1384579087080256968808658741 129804289413774090825811757)
            ·
              refine ⟨48676608530165284059679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129804289413774090825811757 48676608530165284059679409)
              ·
                refine ⟨36507456397623963044759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48676608530165284059679409 36507456397623963044759557)
                ·
                  refine ⟨6845148074554493070892417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36507456397623963044759557 6845148074554493070892417)
                  ·
                    refine ⟨5133861055915869803169313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6845148074554493070892417 5133861055915869803169313)
                    ·
                      refine ⟨3850395791936902352376985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133861055915869803169313 3850395791936902352376985)
                      ·
                        rfl

theorem cell23_7498619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2, 2].length) (baseStart_7498619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498619 prefixEnd_7498619 := by exact prefixLift 7498619
  have htrace : WordTrace (prefixWord ++ tailWord_7498619) baseStart_7498619 baseEnd_7498619 := by
    simpa [prefixWord, tailWord_7498619, baseEnd_7498619] using wordTrace_append hprefix tailTrace_7498619
  have hstable : (prefixWord ++ tailWord_7498619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498619).length < 2 ^ (prefixWord ++ tailWord_7498619).sum := by decide
  have hdescent : baseEnd_7498619 < baseStart_7498619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498665 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_7498665 : Nat := 118140960795 + 7498665 * 2 ^ 59
def prefixEnd_7498665 : Nat := 4983230072969 + 3 ^ 40 * 7498665 * 2
def baseEnd_7498665 : Nat := 3850419412047009172401773

theorem tailTrace_7498665 : CollatzResearch.WordTrace tailWord_7498665 prefixEnd_7498665 3850419412047009172401773 := by
  unfold tailWord_7498665
  simp only [CollatzResearch.WordTrace]
  refine ⟨273498781378624849867761449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182332520919083233245174299 273498781378624849867761449)
  ·
    refine ⟨205124086033968637400821087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273498781378624849867761449 205124086033968637400821087)
    ·
      refine ⟨307686129050952956101231631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205124086033968637400821087 307686129050952956101231631)
      ·
        refine ⟨461529193576429434151847447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307686129050952956101231631 461529193576429434151847447)
        ·
          refine ⟨692293790364644151227771171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461529193576429434151847447 692293790364644151227771171)
          ·
            refine ⟨1038440685546966226841656757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692293790364644151227771171 1038440685546966226841656757)
            ·
              refine ⟨97353814270028083766405321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1038440685546966226841656757 97353814270028083766405321)
              ·
                refine ⟨73015360702521062824803991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97353814270028083766405321 73015360702521062824803991)
                ·
                  refine ⟨109523041053781594237205987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73015360702521062824803991 109523041053781594237205987)
                  ·
                    refine ⟨164284561580672391355808981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109523041053781594237205987 164284561580672391355808981)
                    ·
                      refine ⟨3850419412047009172401773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164284561580672391355808981 3850419412047009172401773)
                      ·
                        rfl

theorem cell23_7498665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_7498665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498665 prefixEnd_7498665 := by exact prefixLift 7498665
  have htrace : WordTrace (prefixWord ++ tailWord_7498665) baseStart_7498665 baseEnd_7498665 := by
    simpa [prefixWord, tailWord_7498665, baseEnd_7498665] using wordTrace_append hprefix tailTrace_7498665
  have hstable : (prefixWord ++ tailWord_7498665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498665).length < 2 ^ (prefixWord ++ tailWord_7498665).sum := by decide
  have hdescent : baseEnd_7498665 < baseStart_7498665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498766 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_7498766 : Nat := 118140960795 + 7498766 * 2 ^ 59
def prefixEnd_7498766 : Nat := 4983230072969 + 3 ^ 40 * 7498766 * 2
def baseEnd_7498766 : Nat := 427830141510345919693201

theorem tailTrace_7498766 : CollatzResearch.WordTrace tailWord_7498766 prefixEnd_7498766 427830141510345919693201 := by
  unfold tailWord_7498766
  simp only [CollatzResearch.WordTrace]
  refine ⟨34187808143907368014648519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182334976767505962744792101 34187808143907368014648519)
  ·
    refine ⟨51281712215861052021972779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34187808143907368014648519 51281712215861052021972779)
    ·
      refine ⟨76922568323791578032959169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51281712215861052021972779 76922568323791578032959169)
      ·
        refine ⟨57691926242843683524719377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76922568323791578032959169 57691926242843683524719377)
        ·
          refine ⟨43268944682132762643539533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57691926242843683524719377 43268944682132762643539533)
          ·
            refine ⟨16225854255799785991327325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43268944682132762643539533 16225854255799785991327325)
            ·
              refine ⟨6084695345924919746747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16225854255799785991327325 6084695345924919746747747)
              ·
                refine ⟨9127043018887379620121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084695345924919746747747 9127043018887379620121621)
                ·
                  refine ⟨427830141510345919693201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9127043018887379620121621 427830141510345919693201)
                  ·
                    rfl

theorem cell23_7498766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_7498766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498766 prefixEnd_7498766 := by exact prefixLift 7498766
  have htrace : WordTrace (prefixWord ++ tailWord_7498766) baseStart_7498766 baseEnd_7498766 := by
    simpa [prefixWord, tailWord_7498766, baseEnd_7498766] using wordTrace_append hprefix tailTrace_7498766
  have hstable : (prefixWord ++ tailWord_7498766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498766).length < 2 ^ (prefixWord ++ tailWord_7498766).sum := by decide
  have hdescent : baseEnd_7498766 < baseStart_7498766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498776 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7498776 : Nat := 118140960795 + 7498776 * 2 ^ 59
def prefixEnd_7498776 : Nat := 4983230072969 + 3 ^ 40 * 7498776 * 2
def baseEnd_7498776 : Nat := 3850476408399658238113763

theorem tailTrace_7498776 : CollatzResearch.WordTrace tailWord_7498776 prefixEnd_7498776 3850476408399658238113763 := by
  unfold tailWord_7498776
  simp only [CollatzResearch.WordTrace]
  refine ⟨136751414940611357912526091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182335219920815143883368121 136751414940611357912526091)
  ·
    refine ⟨205127122410917036868789137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136751414940611357912526091 205127122410917036868789137)
    ·
      refine ⟨153845341808187777651591853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205127122410917036868789137 153845341808187777651591853)
      ·
        refine ⟨57692003178070416619346945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153845341808187777651591853 57692003178070416619346945)
        ·
          refine ⟨43269002383552812464510209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57692003178070416619346945 43269002383552812464510209)
          ·
            refine ⟨32451751787664609348382657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43269002383552812464510209 32451751787664609348382657)
            ·
              refine ⟨24338813840748457011286993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32451751787664609348382657 24338813840748457011286993)
              ·
                refine ⟨18254110380561342758465245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24338813840748457011286993 18254110380561342758465245)
                ·
                  refine ⟨6845291392710503534424467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18254110380561342758465245 6845291392710503534424467)
                  ·
                    refine ⟨10267937089065755301636701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6845291392710503534424467 10267937089065755301636701)
                    ·
                      refine ⟨3850476408399658238113763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10267937089065755301636701 3850476408399658238113763)
                      ·
                        rfl

theorem cell23_7498776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7498776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498776 prefixEnd_7498776 := by exact prefixLift 7498776
  have htrace : WordTrace (prefixWord ++ tailWord_7498776) baseStart_7498776 baseEnd_7498776 := by
    simpa [prefixWord, tailWord_7498776, baseEnd_7498776] using wordTrace_append hprefix tailTrace_7498776
  have hstable : (prefixWord ++ tailWord_7498776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498776).length < 2 ^ (prefixWord ++ tailWord_7498776).sum := by decide
  have hdescent : baseEnd_7498776 < baseStart_7498776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498786 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_7498786 : Nat := 118140960795 + 7498786 * 2 ^ 59
def prefixEnd_7498786 : Nat := 4983230072969 + 3 ^ 40 * 7498786 * 2
def baseEnd_7498786 : Nat := 3850481543206203198988717

theorem tailTrace_7498786 : CollatzResearch.WordTrace tailWord_7498786 prefixEnd_7498786 3850481543206203198988717 := by
  unfold tailWord_7498786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68375798652796621883229053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182335463074124325021944141 68375798652796621883229053)
  ·
    refine ⟨25640924494798733206210895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68375798652796621883229053 25640924494798733206210895)
    ·
      refine ⟨38461386742198099809316343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25640924494798733206210895 38461386742198099809316343)
      ·
        refine ⟨57692080113297149713974515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38461386742198099809316343 57692080113297149713974515)
        ·
          refine ⟨86538120169945724570961773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57692080113297149713974515 86538120169945724570961773)
          ·
            refine ⟨32451795063729646714110665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86538120169945724570961773 32451795063729646714110665)
            ·
              refine ⟨24338846297797235035582999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32451795063729646714110665 24338846297797235035582999)
              ·
                refine ⟨36508269446695852553374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24338846297797235035582999 36508269446695852553374499)
                ·
                  refine ⟨54762404170043778830061749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36508269446695852553374499 54762404170043778830061749)
                  ·
                    refine ⟨5133975390941604265318289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54762404170043778830061749 5133975390941604265318289)
                    ·
                      refine ⟨3850481543206203198988717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5133975390941604265318289 3850481543206203198988717)
                      ·
                        rfl

theorem cell23_7498786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_7498786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498786 prefixEnd_7498786 := by exact prefixLift 7498786
  have htrace : WordTrace (prefixWord ++ tailWord_7498786) baseStart_7498786 baseEnd_7498786 := by
    simpa [prefixWord, tailWord_7498786, baseEnd_7498786] using wordTrace_append hprefix tailTrace_7498786
  have hstable : (prefixWord ++ tailWord_7498786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498786).length < 2 ^ (prefixWord ++ tailWord_7498786).sum := by decide
  have hdescent : baseEnd_7498786 < baseStart_7498786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498819 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3]
def baseStart_7498819 : Nat := 118140960795 + 7498819 * 2 ^ 59
def prefixEnd_7498819 : Nat := 4983230072969 + 3 ^ 40 * 7498819 * 2
def baseEnd_7498819 : Nat := 3850498488067801569876065

theorem tailTrace_7498819 : CollatzResearch.WordTrace tailWord_7498819 prefixEnd_7498819 3850498488067801569876065 := by
  unfold tailWord_7498819
  simp only [CollatzResearch.WordTrace]
  refine ⟨273504398220066934168867511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182336265480044622779245007 273504398220066934168867511)
  ·
    refine ⟨410256597330100401253301267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273504398220066934168867511 410256597330100401253301267)
    ·
      refine ⟨615384895995150601879951901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410256597330100401253301267 615384895995150601879951901)
      ·
        refine ⟨230769335998181475704981963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615384895995150601879951901 230769335998181475704981963)
        ·
          refine ⟨346154003997272213557472945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230769335998181475704981963 346154003997272213557472945)
          ·
            refine ⟨259615502997954160168104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346154003997272213557472945 259615502997954160168104709)
            ·
              refine ⟨48677906812116405031519633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259615502997954160168104709 48677906812116405031519633)
              ·
                refine ⟨36508430109087303773639725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48677906812116405031519633 36508430109087303773639725)
                ·
                  refine ⟨13690661290907738915114897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36508430109087303773639725 13690661290907738915114897)
                  ·
                    refine ⟨10267995968180804186336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13690661290907738915114897 10267995968180804186336173)
                    ·
                      refine ⟨3850498488067801569876065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10267995968180804186336173 3850498488067801569876065)
                      ·
                        rfl

theorem cell23_7498819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_7498819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498819 prefixEnd_7498819 := by exact prefixLift 7498819
  have htrace : WordTrace (prefixWord ++ tailWord_7498819) baseStart_7498819 baseEnd_7498819 := by
    simpa [prefixWord, tailWord_7498819, baseEnd_7498819] using wordTrace_append hprefix tailTrace_7498819
  have hstable : (prefixWord ++ tailWord_7498819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498819).length < 2 ^ (prefixWord ++ tailWord_7498819).sum := by decide
  have hdescent : baseEnd_7498819 < baseStart_7498819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498849 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_7498849 : Nat := 118140960795 + 7498849 * 2 ^ 59
def prefixEnd_7498849 : Nat := 4983230072969 + 3 ^ 40 * 7498849 * 2
def baseEnd_7498849 : Nat := 3850513892487436452500927

theorem tailTrace_7498849 : CollatzResearch.WordTrace tailWord_7498849 prefixEnd_7498849 3850513892487436452500927 := by
  unfold tailWord_7498849
  simp only [CollatzResearch.WordTrace]
  refine ⟨273505492409958249292459601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182336994939972166194973067 273505492409958249292459601)
  ·
    refine ⟨205129119307468686969344701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273505492409958249292459601 205129119307468686969344701)
    ·
      refine ⟨76923419740300757613504263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205129119307468686969344701 76923419740300757613504263)
      ·
        refine ⟨115385129610451136420256395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76923419740300757613504263 115385129610451136420256395)
        ·
          refine ⟨173077694415676704630384593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115385129610451136420256395 173077694415676704630384593)
          ·
            refine ⟨129808270811757528472788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173077694415676704630384593 129808270811757528472788445)
            ·
              refine ⟨48678101554409073177295667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129808270811757528472788445 48678101554409073177295667)
              ·
                refine ⟨73017152331613609765943501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48678101554409073177295667 73017152331613609765943501)
                ·
                  refine ⟨27381432124355103662228813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73017152331613609765943501 27381432124355103662228813)
                  ·
                    refine ⟨10268037046633163873335805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27381432124355103662228813 10268037046633163873335805)
                    ·
                      refine ⟨3850513892487436452500927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268037046633163873335805 3850513892487436452500927)
                      ·
                        rfl

theorem cell23_7498849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_7498849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498849 prefixEnd_7498849 := by exact prefixLift 7498849
  have htrace : WordTrace (prefixWord ++ tailWord_7498849) baseStart_7498849 baseEnd_7498849 := by
    simpa [prefixWord, tailWord_7498849, baseEnd_7498849] using wordTrace_append hprefix tailTrace_7498849
  have hstable : (prefixWord ++ tailWord_7498849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498849).length < 2 ^ (prefixWord ++ tailWord_7498849).sum := by decide
  have hdescent : baseEnd_7498849 < baseStart_7498849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498850 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7498850 : Nat := 118140960795 + 7498850 * 2 ^ 59
def prefixEnd_7498850 : Nat := 4983230072969 + 3 ^ 40 * 7498850 * 2
def baseEnd_7498850 : Nat := 3850514405968090948588423

theorem tailTrace_7498850 : CollatzResearch.WordTrace tailWord_7498850 prefixEnd_7498850 3850514405968090948588423 := by
  unfold tailWord_7498850
  simp only [CollatzResearch.WordTrace]
  refine ⟨68376382220738656615811501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182337019255303084308830669 68376382220738656615811501)
  ·
    refine ⟨25641143332776996230929313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68376382220738656615811501 25641143332776996230929313)
    ·
      refine ⟨19230857499582747173196985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25641143332776996230929313 19230857499582747173196985)
      ·
        refine ⟨14423143124687060379897739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19230857499582747173196985 14423143124687060379897739)
        ·
          refine ⟨21634714687030590569846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14423143124687060379897739 21634714687030590569846609)
          ·
            refine ⟨16226036015272942927384957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21634714687030590569846609 16226036015272942927384957)
            ·
              refine ⟨6084763505727353597769359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16226036015272942927384957 6084763505727353597769359)
              ·
                refine ⟨9127145258591030396654039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084763505727353597769359 9127145258591030396654039)
                ·
                  refine ⟨13690717887886545594981059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127145258591030396654039 13690717887886545594981059)
                  ·
                    refine ⟨20536076831829818392471589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13690717887886545594981059 20536076831829818392471589)
                    ·
                      refine ⟨3850514405968090948588423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20536076831829818392471589 3850514405968090948588423)
                      ·
                        rfl

theorem cell23_7498850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7498850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498850 prefixEnd_7498850 := by exact prefixLift 7498850
  have htrace : WordTrace (prefixWord ++ tailWord_7498850) baseStart_7498850 baseEnd_7498850 := by
    simpa [prefixWord, tailWord_7498850, baseEnd_7498850] using wordTrace_append hprefix tailTrace_7498850
  have hstable : (prefixWord ++ tailWord_7498850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498850).length < 2 ^ (prefixWord ++ tailWord_7498850).sum := by decide
  have hdescent : baseEnd_7498850 < baseStart_7498850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498853 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_7498853 : Nat := 118140960795 + 7498853 * 2 ^ 59
def prefixEnd_7498853 : Nat := 4983230072969 + 3 ^ 40 * 7498853 * 2
def baseEnd_7498853 : Nat := 3850515946410054436850909

theorem tailTrace_7498853 : CollatzResearch.WordTrace tailWord_7498853 prefixEnd_7498853 3850515946410054436850909 := by
  unfold tailWord_7498853
  simp only [CollatzResearch.WordTrace]
  refine ⟨273505638301943757975605213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182337092201295838650403475 273505638301943757975605213)
  ·
    refine ⟨102564614363228909240851955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273505638301943757975605213 102564614363228909240851955)
    ·
      refine ⟨153846921544843363861277933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102564614363228909240851955 153846921544843363861277933)
      ·
        refine ⟨57692595579316261447979225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153846921544843363861277933 57692595579316261447979225)
        ·
          refine ⟨43269446684487196085984419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57692595579316261447979225 43269446684487196085984419)
          ·
            refine ⟨64904170026730794128976629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43269446684487196085984419 64904170026730794128976629)
            ·
              refine ⟨6084765940006011949591559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64904170026730794128976629 6084765940006011949591559)
              ·
                refine ⟨9127148910009017924387339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6084765940006011949591559 9127148910009017924387339)
                ·
                  refine ⟨13690723365013526886581009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127148910009017924387339 13690723365013526886581009)
                  ·
                    refine ⟨10268042523760145164935757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13690723365013526886581009 10268042523760145164935757)
                    ·
                      refine ⟨3850515946410054436850909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268042523760145164935757 3850515946410054436850909)
                      ·
                        rfl

theorem cell23_7498853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_7498853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498853 prefixEnd_7498853 := by exact prefixLift 7498853
  have htrace : WordTrace (prefixWord ++ tailWord_7498853) baseStart_7498853 baseEnd_7498853 := by
    simpa [prefixWord, tailWord_7498853, baseEnd_7498853] using wordTrace_append hprefix tailTrace_7498853
  have hstable : (prefixWord ++ tailWord_7498853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498853).length < 2 ^ (prefixWord ++ tailWord_7498853).sum := by decide
  have hdescent : baseEnd_7498853 < baseStart_7498853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498856 : List Nat := [2, 1, 4, 4, 2, 10]
def baseStart_7498856 : Nat := 118140960795 + 7498856 * 2 ^ 59
def prefixEnd_7498856 : Nat := 4983230072969 + 3 ^ 40 * 7498856 * 2
def baseEnd_7498856 : Nat := 15845750974699662243265

theorem tailTrace_7498856 : CollatzResearch.WordTrace tailWord_7498856 prefixEnd_7498856 15845750974699662243265 := by
  unfold tailWord_7498856
  simp only [CollatzResearch.WordTrace]
  refine ⟨136752873860466444743982211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182337165147288592991976281 136752873860466444743982211)
  ·
    refine ⟨205129310790699667115973317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136752873860466444743982211 205129310790699667115973317)
    ·
      refine ⟨38461745773256187584244997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205129310790699667115973317 38461745773256187584244997)
      ·
        refine ⟨7211577332485535172045937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38461745773256187584244997 7211577332485535172045937)
        ·
          refine ⟨5408682999364151379034453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211577332485535172045937 5408682999364151379034453)
          ·
            refine ⟨15845750974699662243265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5408682999364151379034453 15845750974699662243265)
            ·
              rfl

theorem cell23_7498856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 10].length) (baseStart_7498856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498856 prefixEnd_7498856 := by exact prefixLift 7498856
  have htrace : WordTrace (prefixWord ++ tailWord_7498856) baseStart_7498856 baseEnd_7498856 := by
    simpa [prefixWord, tailWord_7498856, baseEnd_7498856] using wordTrace_append hprefix tailTrace_7498856
  have hstable : (prefixWord ++ tailWord_7498856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498856).length < 2 ^ (prefixWord ++ tailWord_7498856).sum := by decide
  have hdescent : baseEnd_7498856 < baseStart_7498856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498876 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_7498876 : Nat := 118140960795 + 7498876 * 2 ^ 59
def prefixEnd_7498876 : Nat := 4983230072969 + 3 ^ 40 * 7498876 * 2
def baseEnd_7498876 : Nat := 3850527756465107846863303

theorem tailTrace_7498876 : CollatzResearch.WordTrace tailWord_7498876 prefixEnd_7498876 3850527756465107846863303 := by
  unfold tailWord_7498876
  simp only [CollatzResearch.WordTrace]
  refine ⟨136753238590430216451846241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182337651453906955269128321 136753238590430216451846241)
  ·
    refine ⟨102564928942822662338884681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136753238590430216451846241 102564928942822662338884681)
    ·
      refine ⟨76923696707116996754163511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102564928942822662338884681 76923696707116996754163511)
      ·
        refine ⟨115385545060675495131245267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76923696707116996754163511 115385545060675495131245267)
        ·
          refine ⟨173078317591013242696867901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115385545060675495131245267 173078317591013242696867901)
          ·
            refine ⟨64904369096629966011325463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173078317591013242696867901 64904369096629966011325463)
            ·
              refine ⟨97356553644944949016988195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64904369096629966011325463 97356553644944949016988195)
              ·
                refine ⟨146034830467417423525482293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97356553644944949016988195 146034830467417423525482293)
                ·
                  refine ⟨13690765356320383455513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146034830467417423525482293 13690765356320383455513965)
                  ·
                    refine ⟨5134037008620143795817737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13690765356320383455513965 5134037008620143795817737)
                    ·
                      refine ⟨3850527756465107846863303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134037008620143795817737 3850527756465107846863303)
                      ·
                        rfl

theorem cell23_7498876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_7498876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498876 prefixEnd_7498876 := by exact prefixLift 7498876
  have htrace : WordTrace (prefixWord ++ tailWord_7498876) baseStart_7498876 baseEnd_7498876 := by
    simpa [prefixWord, tailWord_7498876, baseEnd_7498876] using wordTrace_append hprefix tailTrace_7498876
  have hstable : (prefixWord ++ tailWord_7498876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498876).length < 2 ^ (prefixWord ++ tailWord_7498876).sum := by decide
  have hdescent : baseEnd_7498876 < baseStart_7498876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498909 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_7498909 : Nat := 118140960795 + 7498909 * 2 ^ 59
def prefixEnd_7498909 : Nat := 4983230072969 + 3 ^ 40 * 7498909 * 2
def baseEnd_7498909 : Nat := 3850544701326706217750651

theorem tailTrace_7498909 : CollatzResearch.WordTrace tailWord_7498909 prefixEnd_7498909 3850544701326706217750651 := by
  unfold tailWord_7498909
  simp only [CollatzResearch.WordTrace]
  refine ⟨273507680789740879539643781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182338453859827253026429187 273507680789740879539643781)
  ·
    refine ⟨51282690148076414913683209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273507680789740879539643781 51282690148076414913683209)
    ·
      refine ⟨38462017611057311185262407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51282690148076414913683209 38462017611057311185262407)
      ·
        refine ⟨57693026416585966777893611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462017611057311185262407 57693026416585966777893611)
        ·
          refine ⟨86539539624878950166840417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57693026416585966777893611 86539539624878950166840417)
          ·
            refine ⟨64904654718659212625130313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86539539624878950166840417 64904654718659212625130313)
            ·
              refine ⟨48678491038994409468847735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64904654718659212625130313 48678491038994409468847735)
              ·
                refine ⟨73017736558491614203271603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48678491038994409468847735 73017736558491614203271603)
                ·
                  refine ⟨109526604837737421304907405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73017736558491614203271603 109526604837737421304907405)
                  ·
                    refine ⟨41072476814151532989340277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109526604837737421304907405 41072476814151532989340277)
                    ·
                      refine ⟨3850544701326706217750651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41072476814151532989340277 3850544701326706217750651)
                      ·
                        rfl

theorem cell23_7498909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_7498909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498909 prefixEnd_7498909 := by exact prefixLift 7498909
  have htrace : WordTrace (prefixWord ++ tailWord_7498909) baseStart_7498909 baseEnd_7498909 := by
    simpa [prefixWord, tailWord_7498909, baseEnd_7498909] using wordTrace_append hprefix tailTrace_7498909
  have hstable : (prefixWord ++ tailWord_7498909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498909).length < 2 ^ (prefixWord ++ tailWord_7498909).sum := by decide
  have hdescent : baseEnd_7498909 < baseStart_7498909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498934 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7498934 : Nat := 118140960795 + 7498934 * 2 ^ 59
def prefixEnd_7498934 : Nat := 4983230072969 + 3 ^ 40 * 7498934 * 2
def baseEnd_7498934 : Nat := 3850557538343068619938037

theorem tailTrace_7498934 : CollatzResearch.WordTrace tailWord_7498934 prefixEnd_7498934 3850557538343068619938037 := by
  unfold tailWord_7498934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17094287038415644300581491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182339061743100205872869237 17094287038415644300581491)
  ·
    refine ⟨25641430557623466450872237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17094287038415644300581491 25641430557623466450872237)
    ·
      refine ⟨9615536459108799919077089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25641430557623466450872237 9615536459108799919077089)
      ·
        refine ⟨7211652344331599939307817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9615536459108799919077089 7211652344331599939307817)
        ·
          refine ⟨5408739258248699954480863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211652344331599939307817 5408739258248699954480863)
          ·
            refine ⟨8113108887373049931721295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408739258248699954480863 8113108887373049931721295)
            ·
              refine ⟨12169663331059574897581943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113108887373049931721295 12169663331059574897581943)
              ·
                refine ⟨18254494996589362346372915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169663331059574897581943 18254494996589362346372915)
                ·
                  refine ⟨27381742494884043519559373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18254494996589362346372915 27381742494884043519559373)
                  ·
                    refine ⟨10268153435581516319834765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27381742494884043519559373 10268153435581516319834765)
                    ·
                      refine ⟨3850557538343068619938037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268153435581516319834765 3850557538343068619938037)
                      ·
                        rfl

theorem cell23_7498934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7498934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498934 prefixEnd_7498934 := by exact prefixLift 7498934
  have htrace : WordTrace (prefixWord ++ tailWord_7498934) baseStart_7498934 baseEnd_7498934 := by
    simpa [prefixWord, tailWord_7498934, baseEnd_7498934] using wordTrace_append hprefix tailTrace_7498934
  have hstable : (prefixWord ++ tailWord_7498934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498934).length < 2 ^ (prefixWord ++ tailWord_7498934).sum := by decide
  have hdescent : baseEnd_7498934 < baseStart_7498934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498939 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3]
def baseStart_7498939 : Nat := 118140960795 + 7498939 * 2 ^ 59
def prefixEnd_7498939 : Nat := 4983230072969 + 3 ^ 40 * 7498939 * 2
def baseEnd_7498939 : Nat := 3850560105746341100375513

theorem tailTrace_7498939 : CollatzResearch.WordTrace tailWord_7498939 prefixEnd_7498939 3850560105746341100375513 := by
  unfold tailWord_7498939
  simp only [CollatzResearch.WordTrace]
  refine ⟨273508774979632194663235871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182339183319754796442157247 273508774979632194663235871)
  ·
    refine ⟨410263162469448291994853807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273508774979632194663235871 410263162469448291994853807)
    ·
      refine ⟨615394743704172437992280711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410263162469448291994853807 615394743704172437992280711)
      ·
        refine ⟨923092115556258656988421067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615394743704172437992280711 923092115556258656988421067)
        ·
          refine ⟨1384638173334387985482631601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923092115556258656988421067 1384638173334387985482631601)
          ·
            refine ⟨1038478630000790989111973701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384638173334387985482631601 1038478630000790989111973701)
            ·
              refine ⟨194714743125148310458495069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1038478630000790989111973701 194714743125148310458495069)
              ·
                refine ⟨73018028671930616421935651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194714743125148310458495069 73018028671930616421935651)
                ·
                  refine ⟨109527043007895924632903477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73018028671930616421935651 109527043007895924632903477)
                  ·
                    refine ⟨10268160281990242934334701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109527043007895924632903477 10268160281990242934334701)
                    ·
                      refine ⟨3850560105746341100375513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268160281990242934334701 3850560105746341100375513)
                      ·
                        rfl

theorem cell23_7498939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].length) (baseStart_7498939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498939 prefixEnd_7498939 := by exact prefixLift 7498939
  have htrace : WordTrace (prefixWord ++ tailWord_7498939) baseStart_7498939 baseEnd_7498939 := by
    simpa [prefixWord, tailWord_7498939, baseEnd_7498939] using wordTrace_append hprefix tailTrace_7498939
  have hstable : (prefixWord ++ tailWord_7498939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498939).length < 2 ^ (prefixWord ++ tailWord_7498939).sum := by decide
  have hdescent : baseEnd_7498939 < baseStart_7498939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498940 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_7498940 : Nat := 118140960795 + 7498940 * 2 ^ 59
def prefixEnd_7498940 : Nat := 4983230072969 + 3 ^ 40 * 7498940 * 2
def baseEnd_7498940 : Nat := 3850560619226995596463009

theorem tailTrace_7498940 : CollatzResearch.WordTrace tailWord_7498940 prefixEnd_7498940 3850560619226995596463009 := by
  unfold tailWord_7498940
  simp only [CollatzResearch.WordTrace]
  refine ⟨136754405726314285917011137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182339207635085714556014849 136754405726314285917011137)
  ·
    refine ⟨102565804294735714437758353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136754405726314285917011137 102565804294735714437758353)
    ·
      refine ⟨76924353221051785828318765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102565804294735714437758353 76924353221051785828318765)
      ·
        refine ⟨28846632457894419685619537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76924353221051785828318765 28846632457894419685619537)
        ·
          refine ⟨21634974343420814764214653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28846632457894419685619537 21634974343420814764214653)
          ·
            refine ⟨8113115378782805536580495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21634974343420814764214653 8113115378782805536580495)
            ·
              refine ⟨12169673068174208304870743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113115378782805536580495 12169673068174208304870743)
              ·
                refine ⟨18254509602261312457306115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169673068174208304870743 18254509602261312457306115)
                ·
                  refine ⟨27381764403391968685959173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18254509602261312457306115 27381764403391968685959173)
                  ·
                    refine ⟨5134080825635994128617345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27381764403391968685959173 5134080825635994128617345)
                    ·
                      refine ⟨3850560619226995596463009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134080825635994128617345 3850560619226995596463009)
                      ·
                        rfl

theorem cell23_7498940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_7498940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498940 prefixEnd_7498940 := by exact prefixLift 7498940
  have htrace : WordTrace (prefixWord ++ tailWord_7498940) baseStart_7498940 baseEnd_7498940 := by
    simpa [prefixWord, tailWord_7498940, baseEnd_7498940] using wordTrace_append hprefix tailTrace_7498940
  have hstable : (prefixWord ++ tailWord_7498940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498940).length < 2 ^ (prefixWord ++ tailWord_7498940).sum := by decide
  have hdescent : baseEnd_7498940 < baseStart_7498940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498969 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7498969 : Nat := 118140960795 + 7498969 * 2 ^ 59
def prefixEnd_7498969 : Nat := 4983230072969 + 3 ^ 40 * 7498969 * 2
def baseEnd_7498969 : Nat := 3850575510165975983000375

theorem tailTrace_7498969 : CollatzResearch.WordTrace tailWord_7498969 prefixEnd_7498969 3850575510165975983000375 := by
  unfold tailWord_7498969
  simp only [CollatzResearch.WordTrace]
  refine ⟨273509869169523509786827961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182339912779682339857885307 273509869169523509786827961)
  ·
    refine ⟨205132401877142632340120971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273509869169523509786827961 205132401877142632340120971)
    ·
      refine ⟨307698602815713948510181457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205132401877142632340120971 307698602815713948510181457)
      ·
        refine ⟨230773952111785461382636093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307698602815713948510181457 230773952111785461382636093)
        ·
          refine ⟨86540232041919548018488535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230773952111785461382636093 86540232041919548018488535)
          ·
            refine ⟨129810348062879322027732803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86540232041919548018488535 129810348062879322027732803)
            ·
              refine ⟨194715522094318983041599205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129810348062879322027732803 194715522094318983041599205)
              ·
                refine ⟨36509160392684809320299851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194715522094318983041599205 36509160392684809320299851)
                ·
                  refine ⟨54763740589027213980449777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36509160392684809320299851 54763740589027213980449777)
                  ·
                    refine ⟨41072805441770410485337333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54763740589027213980449777 41072805441770410485337333)
                    ·
                      refine ⟨3850575510165975983000375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41072805441770410485337333 3850575510165975983000375)
                      ·
                        rfl

theorem cell23_7498969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7498969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498969 prefixEnd_7498969 := by exact prefixLift 7498969
  have htrace : WordTrace (prefixWord ++ tailWord_7498969) baseStart_7498969 baseEnd_7498969 := by
    simpa [prefixWord, tailWord_7498969, baseEnd_7498969] using wordTrace_append hprefix tailTrace_7498969
  have hstable : (prefixWord ++ tailWord_7498969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498969).length < 2 ^ (prefixWord ++ tailWord_7498969).sum := by decide
  have hdescent : baseEnd_7498969 < baseStart_7498969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498976 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_7498976 : Nat := 118140960795 + 7498976 * 2 ^ 59
def prefixEnd_7498976 : Nat := 4983230072969 + 3 ^ 40 * 7498976 * 2
def baseEnd_7498976 : Nat := 1283526368176852485204281

theorem tailTrace_7498976 : CollatzResearch.WordTrace tailWord_7498976 prefixEnd_7498976 1283526368176852485204281 := by
  unfold tailWord_7498976
  simp only [CollatzResearch.WordTrace]
  refine ⟨136755062240249074991166391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182340082986998766654888521 136755062240249074991166391)
  ·
    refine ⟨205132593360373612486749587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136755062240249074991166391 205132593360373612486749587)
    ·
      refine ⟨307698890040560418730124381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205132593360373612486749587 307698890040560418730124381)
      ·
        refine ⟨115387083765210157023796643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307698890040560418730124381 115387083765210157023796643)
        ·
          refine ⟨173080625647815235535694965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115387083765210157023796643 173080625647815235535694965)
          ·
            refine ⟨16226308654482678331471403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173080625647815235535694965 16226308654482678331471403)
            ·
              refine ⟨24339462981724017497207105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226308654482678331471403 24339462981724017497207105)
              ·
                refine ⟨18254597236293013122905329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24339462981724017497207105 18254597236293013122905329)
                ·
                  refine ⟨13690947927219759842178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18254597236293013122905329 13690947927219759842178997)
                  ·
                    refine ⟨1283526368176852485204281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13690947927219759842178997 1283526368176852485204281)
                    ·
                      rfl

theorem cell23_7498976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_7498976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498976 prefixEnd_7498976 := by exact prefixLift 7498976
  have htrace : WordTrace (prefixWord ++ tailWord_7498976) baseStart_7498976 baseEnd_7498976 := by
    simpa [prefixWord, tailWord_7498976, baseEnd_7498976] using wordTrace_append hprefix tailTrace_7498976
  have hstable : (prefixWord ++ tailWord_7498976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498976).length < 2 ^ (prefixWord ++ tailWord_7498976).sum := by decide
  have hdescent : baseEnd_7498976 < baseStart_7498976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7498986 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_7498986 : Nat := 118140960795 + 7498986 * 2 ^ 59
def prefixEnd_7498986 : Nat := 4983230072969 + 3 ^ 40 * 7498986 * 2
def baseEnd_7498986 : Nat := 3850584239337102416487797

theorem tailTrace_7498986 : CollatzResearch.WordTrace tailWord_7498986 prefixEnd_7498986 3850584239337102416487797 := by
  unfold tailWord_7498986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68377622302615480422549203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182340326140307947793464541 68377622302615480422549203)
  ·
    refine ⟨102566433453923220633823805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68377622302615480422549203 102566433453923220633823805)
    ·
      refine ⟨38462412545221207737683927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102566433453923220633823805 38462412545221207737683927)
      ·
        refine ⟨57693618817831811606525891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462412545221207737683927 57693618817831811606525891)
        ·
          refine ⟨86540428226747717409788837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57693618817831811606525891 86540428226747717409788837)
          ·
            refine ⟨16226330292515197014335407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86540428226747717409788837 16226330292515197014335407)
            ·
              refine ⟨24339495438772795521503111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226330292515197014335407 24339495438772795521503111)
              ·
                refine ⟨36509243158159193282254667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24339495438772795521503111 36509243158159193282254667)
                ·
                  refine ⟨54763864737238789923382001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36509243158159193282254667 54763864737238789923382001)
                  ·
                    refine ⟨41072898552929092442536501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54763864737238789923382001 41072898552929092442536501)
                    ·
                      refine ⟨3850584239337102416487797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41072898552929092442536501 3850584239337102416487797)
                      ·
                        rfl

theorem cell23_7498986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_7498986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7498986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7498986 prefixEnd_7498986 := by exact prefixLift 7498986
  have htrace : WordTrace (prefixWord ++ tailWord_7498986) baseStart_7498986 baseEnd_7498986 := by
    simpa [prefixWord, tailWord_7498986, baseEnd_7498986] using wordTrace_append hprefix tailTrace_7498986
  have hstable : (prefixWord ++ tailWord_7498986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7498986).length < 2 ^ (prefixWord ++ tailWord_7498986).sum := by decide
  have hdescent : baseEnd_7498986 < baseStart_7498986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7498986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499010 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_7499010 : Nat := 118140960795 + 7499010 * 2 ^ 59
def prefixEnd_7499010 : Nat := 4983230072969 + 3 ^ 40 * 7499010 * 2
def baseEnd_7499010 : Nat := 1283532187624270107529229

theorem tailTrace_7499010 : CollatzResearch.WordTrace tailWord_7499010 prefixEnd_7499010 1283532187624270107529229 := by
  unfold tailWord_7499010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68377841140593743447267621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182340909708249982526046989 68377841140593743447267621)
  ·
    refine ⟨12820845213861326896362679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68377841140593743447267621 12820845213861326896362679)
    ·
      refine ⟨19231267820791990344544019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12820845213861326896362679 19231267820791990344544019)
      ·
        refine ⟨28846901731187985516816029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231267820791990344544019 28846901731187985516816029)
        ·
          refine ⟨10817588149195494568806011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28846901731187985516816029 10817588149195494568806011)
          ·
            refine ⟨16226382223793241853209017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817588149195494568806011 16226382223793241853209017)
            ·
              refine ⟨12169786667844931389906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16226382223793241853209017 12169786667844931389906763)
              ·
                refine ⟨18254680001767397084860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12169786667844931389906763 18254680001767397084860145)
                ·
                  refine ⟨13691010001325547813645109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18254680001767397084860145 13691010001325547813645109)
                  ·
                    refine ⟨1283532187624270107529229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13691010001325547813645109 1283532187624270107529229)
                    ·
                      rfl

theorem cell23_7499010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_7499010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499010 prefixEnd_7499010 := by exact prefixLift 7499010
  have htrace : WordTrace (prefixWord ++ tailWord_7499010) baseStart_7499010 baseEnd_7499010 := by
    simpa [prefixWord, tailWord_7499010, baseEnd_7499010] using wordTrace_append hprefix tailTrace_7499010
  have hstable : (prefixWord ++ tailWord_7499010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499010).length < 2 ^ (prefixWord ++ tailWord_7499010).sum := by decide
  have hdescent : baseEnd_7499010 < baseStart_7499010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499036 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 6]
def baseStart_7499036 : Nat := 118140960795 + 7499036 * 2 ^ 59
def prefixEnd_7499036 : Nat := 4983230072969 + 3 ^ 40 * 7499036 * 2
def baseEnd_7499036 : Nat := 427845545929980802318063

theorem tailTrace_7499036 : CollatzResearch.WordTrace tailWord_7499036 prefixEnd_7499036 427845545929980802318063 := by
  unfold tailWord_7499036
  simp only [CollatzResearch.WordTrace]
  refine ⟨136756156430140390114758481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182341541906853853486344641 136756156430140390114758481)
  ·
    refine ⟨102567117322605292586068861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136756156430140390114758481 102567117322605292586068861)
    ·
      refine ⟨38462668995976984719775823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102567117322605292586068861 38462668995976984719775823)
      ·
        refine ⟨57694003493965477079663735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38462668995976984719775823 57694003493965477079663735)
        ·
          refine ⟨86541005240948215619495603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57694003493965477079663735 86541005240948215619495603)
          ·
            refine ⟨129811507861422323429243405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86541005240948215619495603 129811507861422323429243405)
            ·
              refine ⟨48679315448033371285966277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129811507861422323429243405 48679315448033371285966277)
              ·
                refine ⟨9127371646506257116118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48679315448033371285966277 9127371646506257116118677)
                ·
                  refine ⟨427845545929980802318063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9127371646506257116118677 427845545929980802318063)
                  ·
                    rfl

theorem cell23_7499036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_7499036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499036 prefixEnd_7499036 := by exact prefixLift 7499036
  have htrace : WordTrace (prefixWord ++ tailWord_7499036) baseStart_7499036 baseEnd_7499036 := by
    simpa [prefixWord, tailWord_7499036, baseEnd_7499036] using wordTrace_append hprefix tailTrace_7499036
  have hstable : (prefixWord ++ tailWord_7499036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499036).length < 2 ^ (prefixWord ++ tailWord_7499036).sum := by decide
  have hdescent : baseEnd_7499036 < baseStart_7499036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499066 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_7499066 : Nat := 118140960795 + 7499066 * 2 ^ 59
def prefixEnd_7499066 : Nat := 4983230072969 + 3 ^ 40 * 7499066 * 2
def baseEnd_7499066 : Nat := 1283541772596487367829143

theorem tailTrace_7499066 : CollatzResearch.WordTrace tailWord_7499066 prefixEnd_7499066 1283541772596487367829143 := by
  unfold tailWord_7499066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68378351762543023838277263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182342271366781396902072701 68378351762543023838277263)
  ·
    refine ⟨102567527643814535757415895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68378351762543023838277263 102567527643814535757415895)
    ·
      refine ⟨153851291465721803636123843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102567527643814535757415895 153851291465721803636123843)
      ·
        refine ⟨230776937198582705454185765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153851291465721803636123843 230776937198582705454185765)
        ·
          refine ⟨43270675724734257272659831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230776937198582705454185765 43270675724734257272659831)
          ·
            refine ⟨64906013587101385908989747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43270675724734257272659831 64906013587101385908989747)
            ·
              refine ⟨97359020380652078863484621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64906013587101385908989747 97359020380652078863484621)
              ·
                refine ⟨36509632642744529573806733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97359020380652078863484621 36509632642744529573806733)
                ·
                  refine ⟨13691112241029198590177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36509632642744529573806733 13691112241029198590177525)
                  ·
                    refine ⟨1283541772596487367829143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13691112241029198590177525 1283541772596487367829143)
                    ·
                      rfl

theorem cell23_7499066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_7499066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499066 prefixEnd_7499066 := by exact prefixLift 7499066
  have htrace : WordTrace (prefixWord ++ tailWord_7499066) baseStart_7499066 baseEnd_7499066 := by
    simpa [prefixWord, tailWord_7499066, baseEnd_7499066] using wordTrace_append hprefix tailTrace_7499066
  have hstable : (prefixWord ++ tailWord_7499066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499066).length < 2 ^ (prefixWord ++ tailWord_7499066).sum := by decide
  have hdescent : baseEnd_7499066 < baseStart_7499066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499120 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2]
def baseStart_7499120 : Nat := 118140960795 + 7499120 * 2 ^ 59
def prefixEnd_7499120 : Nat := 4983230072969 + 3 ^ 40 * 7499120 * 2
def baseEnd_7499120 : Nat := 3850653045744804892212181

theorem tailTrace_7499120 : CollatzResearch.WordTrace tailWord_7499120 prefixEnd_7499120 3850653045744804892212181 := by
  unfold tailWord_7499120
  simp only [CollatzResearch.WordTrace]
  refine ⟨136757688295988231287787407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182343584394650975050383209 136757688295988231287787407)
  ·
    refine ⟨205136532443982346931681111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136757688295988231287787407 205136532443982346931681111)
    ·
      refine ⟨307704798665973520397521667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205136532443982346931681111 307704798665973520397521667)
      ·
        refine ⟨461557197998960280596282501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307704798665973520397521667 461557197998960280596282501)
        ·
          refine ⟨86541974624805052611802969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461557197998960280596282501 86541974624805052611802969)
          ·
            refine ⟨64906480968603789458852227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86541974624805052611802969 64906480968603789458852227)
            ·
              refine ⟨97359721452905684188278341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64906480968603789458852227 97359721452905684188278341)
              ·
                refine ⟨18254947772419815785302189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97359721452905684188278341 18254947772419815785302189)
                ·
                  refine ⟨6845605414657430919488321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18254947772419815785302189 6845605414657430919488321)
                  ·
                    refine ⟨5134204060993073189616241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6845605414657430919488321 5134204060993073189616241)
                    ·
                      refine ⟨3850653045744804892212181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134204060993073189616241 3850653045744804892212181)
                      ·
                        rfl

theorem cell23_7499120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 2, 2].length) (baseStart_7499120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499120 prefixEnd_7499120 := by exact prefixLift 7499120
  have htrace : WordTrace (prefixWord ++ tailWord_7499120) baseStart_7499120 baseEnd_7499120 := by
    simpa [prefixWord, tailWord_7499120, baseEnd_7499120] using wordTrace_append hprefix tailTrace_7499120
  have hstable : (prefixWord ++ tailWord_7499120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499120).length < 2 ^ (prefixWord ++ tailWord_7499120).sum := by decide
  have hdescent : baseEnd_7499120 < baseStart_7499120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499140 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7499140 : Nat := 118140960795 + 7499140 * 2 ^ 59
def prefixEnd_7499140 : Nat := 4983230072969 + 3 ^ 40 * 7499140 * 2
def baseEnd_7499140 : Nat := 3850663315357894813962089

theorem tailTrace_7499140 : CollatzResearch.WordTrace tailWord_7499140 prefixEnd_7499140 3850663315357894813962089 := by
  unfold tailWord_7499140
  simp only [CollatzResearch.WordTrace]
  refine ⟨136758053025952002995651437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182344070701269337327535249 136758053025952002995651437)
  ·
    refine ⟨51284269884732001123369289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136758053025952002995651437 51284269884732001123369289)
    ·
      refine ⟨38463202413549000842526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51284269884732001123369289 38463202413549000842526967)
      ·
        refine ⟨57694803620323501263790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38463202413549000842526967 57694803620323501263790451)
        ·
          refine ⟨86542205430485251895685677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57694803620323501263790451 86542205430485251895685677)
          ·
            refine ⟨32453327036431969460882129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86542205430485251895685677 32453327036431969460882129)
            ·
              refine ⟨24339995277323977095661597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32453327036431969460882129 24339995277323977095661597)
              ·
                refine ⟨9127498228996491410873099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24339995277323977095661597 9127498228996491410873099)
                ·
                  refine ⟨13691247343494737116309649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127498228996491410873099 13691247343494737116309649)
                  ·
                    refine ⟨10268435507621052837232237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13691247343494737116309649 10268435507621052837232237)
                    ·
                      refine ⟨3850663315357894813962089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268435507621052837232237 3850663315357894813962089)
                      ·
                        rfl

theorem cell23_7499140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7499140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499140 prefixEnd_7499140 := by exact prefixLift 7499140
  have htrace : WordTrace (prefixWord ++ tailWord_7499140) baseStart_7499140 baseEnd_7499140 := by
    simpa [prefixWord, tailWord_7499140, baseEnd_7499140] using wordTrace_append hprefix tailTrace_7499140
  have hstable : (prefixWord ++ tailWord_7499140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499140).length < 2 ^ (prefixWord ++ tailWord_7499140).sum := by decide
  have hdescent : baseEnd_7499140 < baseStart_7499140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499186 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_7499186 : Nat := 118140960795 + 7499186 * 2 ^ 59
def prefixEnd_7499186 : Nat := 4983230072969 + 3 ^ 40 * 7499186 * 2
def baseEnd_7499186 : Nat := 1283562311822667211328959

theorem tailTrace_7499186 : CollatzResearch.WordTrace tailWord_7499186 prefixEnd_7499186 1283562311822667211328959 := by
  unfold tailWord_7499186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68379445952434338961869353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182345189206491570564984941 68379445952434338961869353)
  ·
    refine ⟨51284584464325754221402015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68379445952434338961869353 51284584464325754221402015)
    ·
      refine ⟨76926876696488631332103023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51284584464325754221402015 76926876696488631332103023)
      ·
        refine ⟨115390315044732946998154535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76926876696488631332103023 115390315044732946998154535)
        ·
          refine ⟨173085472567099420497231803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115390315044732946998154535 173085472567099420497231803)
          ·
            refine ⟨259628208850649130745847705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173085472567099420497231803 259628208850649130745847705)
            ·
              refine ⟨194721156637986848059385779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259628208850649130745847705 194721156637986848059385779)
              ·
                refine ⟨292081734956980272089078669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194721156637986848059385779 292081734956980272089078669)
                ·
                  refine ⟨109530650608867602033404501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292081734956980272089078669 109530650608867602033404501)
                  ·
                    refine ⟨1283562311822667211328959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109530650608867602033404501 1283562311822667211328959)
                    ·
                      rfl

theorem cell23_7499186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_7499186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499186 prefixEnd_7499186 := by exact prefixLift 7499186
  have htrace : WordTrace (prefixWord ++ tailWord_7499186) baseStart_7499186 baseEnd_7499186 := by
    simpa [prefixWord, tailWord_7499186, baseEnd_7499186] using wordTrace_append hprefix tailTrace_7499186
  have hstable : (prefixWord ++ tailWord_7499186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499186).length < 2 ^ (prefixWord ++ tailWord_7499186).sum := by decide
  have hdescent : baseEnd_7499186 < baseStart_7499186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499204 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7499204 : Nat := 118140960795 + 7499204 * 2 ^ 59
def prefixEnd_7499204 : Nat := 4983230072969 + 3 ^ 40 * 7499204 * 2
def baseEnd_7499204 : Nat := 3850696178119782563561795

theorem tailTrace_7499204 : CollatzResearch.WordTrace tailWord_7499204 prefixEnd_7499204 3850696178119782563561795 := by
  unfold tailWord_7499204
  simp only [CollatzResearch.WordTrace]
  refine ⟨136759220161836072460816333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182345626882448096614421777 136759220161836072460816333)
  ·
    refine ⟨51284707560688527172806125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136759220161836072460816333 51284707560688527172806125)
    ·
      refine ⟨19231765335258197689802297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51284707560688527172806125 19231765335258197689802297)
      ·
        refine ⟨14423824001443648267351723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19231765335258197689802297 14423824001443648267351723)
        ·
          refine ⟨21635736002165472401027585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14423824001443648267351723 21635736002165472401027585)
          ·
            refine ⟨16226802001624104300770689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21635736002165472401027585 16226802001624104300770689)
            ·
              refine ⟨12170101501218078225578017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16226802001624104300770689 12170101501218078225578017)
              ·
                refine ⟨9127576125913558669183513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12170101501218078225578017 9127576125913558669183513)
                ·
                  refine ⟨6845682094435169001887635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9127576125913558669183513 6845682094435169001887635)
                  ·
                    refine ⟨10268523141652753502831453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6845682094435169001887635 10268523141652753502831453)
                    ·
                      refine ⟨3850696178119782563561795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268523141652753502831453 3850696178119782563561795)
                      ·
                        rfl

theorem cell23_7499204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7499204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499204 prefixEnd_7499204 := by exact prefixLift 7499204
  have htrace : WordTrace (prefixWord ++ tailWord_7499204) baseStart_7499204 baseEnd_7499204 := by
    simpa [prefixWord, tailWord_7499204, baseEnd_7499204] using wordTrace_append hprefix tailTrace_7499204
  have hstable : (prefixWord ++ tailWord_7499204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499204).length < 2 ^ (prefixWord ++ tailWord_7499204).sum := by decide
  have hdescent : baseEnd_7499204 < baseStart_7499204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499220 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_7499220 : Nat := 118140960795 + 7499220 * 2 ^ 59
def prefixEnd_7499220 : Nat := 4983230072969 + 3 ^ 40 * 7499220 * 2
def baseEnd_7499220 : Nat := 1283568131270084833653907

theorem tailTrace_7499220 : CollatzResearch.WordTrace tailWord_7499220 prefixEnd_7499220 1283568131270084833653907 := by
  unfold tailWord_7499220
  simp only [CollatzResearch.WordTrace]
  refine ⟨136759511945807089827107557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182346015927742786436143409 136759511945807089827107557)
  ·
    refine ⟨25642408489838829342582667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136759511945807089827107557 25642408489838829342582667)
    ·
      refine ⟨38463612734758244013874001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25642408489838829342582667 38463612734758244013874001)
      ·
        refine ⟨28847709551068683010405501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38463612734758244013874001 28847709551068683010405501)
        ·
          refine ⟨10817891081650756128902063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28847709551068683010405501 10817891081650756128902063)
          ·
            refine ⟨16226836622476134193353095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817891081650756128902063 16226836622476134193353095)
            ·
              refine ⟨24340254933714201290029643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226836622476134193353095 24340254933714201290029643)
              ·
                refine ⟨36510382400571301935044465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24340254933714201290029643 36510382400571301935044465)
                ·
                  refine ⟨27382786800428476451283349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36510382400571301935044465 27382786800428476451283349)
                  ·
                    refine ⟨1283568131270084833653907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27382786800428476451283349 1283568131270084833653907)
                    ·
                      rfl

theorem cell23_7499220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_7499220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499220 prefixEnd_7499220 := by exact prefixLift 7499220
  have htrace : WordTrace (prefixWord ++ tailWord_7499220) baseStart_7499220 baseEnd_7499220 := by
    simpa [prefixWord, tailWord_7499220, baseEnd_7499220] using wordTrace_append hprefix tailTrace_7499220
  have hstable : (prefixWord ++ tailWord_7499220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499220).length < 2 ^ (prefixWord ++ tailWord_7499220).sum := by decide
  have hdescent : baseEnd_7499220 < baseStart_7499220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499233 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 7]
def baseStart_7499233 : Nat := 118140960795 + 7499233 * 2 ^ 59
def prefixEnd_7499233 : Nat := 4983230072969 + 3 ^ 40 * 7499233 * 2
def baseEnd_7499233 : Nat := 427856785450973661122129

theorem tailTrace_7499233 : CollatzResearch.WordTrace tailWord_7499233 prefixEnd_7499233 427856785450973661122129 := by
  unfold tailWord_7499233
  simp only [CollatzResearch.WordTrace]
  refine ⟨273519498040567082874438353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182346332027044721916292235 273519498040567082874438353)
  ·
    refine ⟨205139623530425312155828765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273519498040567082874438353 205139623530425312155828765)
    ·
      refine ⟨76927358823909492058435787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205139623530425312155828765 76927358823909492058435787)
      ·
        refine ⟨115391038235864238087653681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76927358823909492058435787 115391038235864238087653681)
        ·
          refine ⟨86543278676898178565740261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115391038235864238087653681 86543278676898178565740261)
          ·
            refine ⟨16226864751918408481076299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86543278676898178565740261 16226864751918408481076299)
            ·
              refine ⟨24340297127877612721614449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226864751918408481076299 24340297127877612721614449)
              ·
                refine ⟨18255222845908209541210837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24340297127877612721614449 18255222845908209541210837)
                ·
                  refine ⟨427856785450973661122129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18255222845908209541210837 427856785450973661122129)
                  ·
                    rfl

theorem cell23_7499233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_7499233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499233 prefixEnd_7499233 := by exact prefixLift 7499233
  have htrace : WordTrace (prefixWord ++ tailWord_7499233) baseStart_7499233 baseEnd_7499233 := by
    simpa [prefixWord, tailWord_7499233, baseEnd_7499233] using wordTrace_append hprefix tailTrace_7499233
  have hstable : (prefixWord ++ tailWord_7499233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499233).length < 2 ^ (prefixWord ++ tailWord_7499233).sum := by decide
  have hdescent : baseEnd_7499233 < baseStart_7499233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499283 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_7499283 : Nat := 118140960795 + 7499283 * 2 ^ 59
def prefixEnd_7499283 : Nat := 4983230072969 + 3 ^ 40 * 7499283 * 2
def baseEnd_7499283 : Nat := 3850736743091487754473931

theorem tailTrace_7499283 : CollatzResearch.WordTrace tailWord_7499283 prefixEnd_7499283 3850736743091487754473931 := by
  unfold tailWord_7499283
  simp only [CollatzResearch.WordTrace]
  refine ⟨273521321690385941413758503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182347547793590627609172335 273521321690385941413758503)
  ·
    refine ⟨410281982535578912120637755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273521321690385941413758503 410281982535578912120637755)
    ·
      refine ⟨615422973803368368180956633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410281982535578912120637755 615422973803368368180956633)
      ·
        refine ⟨461567230352526276135717475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615422973803368368180956633 461567230352526276135717475)
        ·
          refine ⟨692350845528789414203576213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461567230352526276135717475 692350845528789414203576213)
          ·
            refine ⟨32453945884162003790792635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 692350845528789414203576213 32453945884162003790792635)
            ·
              refine ⟨48680918826243005686188953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32453945884162003790792635 48680918826243005686188953)
              ·
                refine ⟨36510689119682254264641715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48680918826243005686188953 36510689119682254264641715)
                ·
                  refine ⟨54766033679523381396962573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36510689119682254264641715 54766033679523381396962573)
                  ·
                    refine ⟨20537262629821268023860965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54766033679523381396962573 20537262629821268023860965)
                    ·
                      refine ⟨3850736743091487754473931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20537262629821268023860965 3850736743091487754473931)
                      ·
                        rfl

theorem cell23_7499283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_7499283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499283 prefixEnd_7499283 := by exact prefixLift 7499283
  have htrace : WordTrace (prefixWord ++ tailWord_7499283) baseStart_7499283 baseEnd_7499283 := by
    simpa [prefixWord, tailWord_7499283, baseEnd_7499283] using wordTrace_append hprefix tailTrace_7499283
  have hstable : (prefixWord ++ tailWord_7499283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499283).length < 2 ^ (prefixWord ++ tailWord_7499283).sum := by decide
  have hdescent : baseEnd_7499283 < baseStart_7499283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499293 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_7499293 : Nat := 118140960795 + 7499293 * 2 ^ 59
def prefixEnd_7499293 : Nat := 4983230072969 + 3 ^ 40 * 7499293 * 2
def baseEnd_7499293 : Nat := 1283580625966010905116295

theorem tailTrace_7499293 : CollatzResearch.WordTrace tailWord_7499293 prefixEnd_7499293 1283580625966010905116295 := by
  unfold tailWord_7499293
  simp only [CollatzResearch.WordTrace]
  refine ⟨273521686420349713121622533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182347790946899808747748355 273521686420349713121622533)
  ·
    refine ⟨51285316203815571210304225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273521686420349713121622533 51285316203815571210304225)
    ·
      refine ⟨38463987152861678407728169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51285316203815571210304225 38463987152861678407728169)
      ·
        refine ⟨28847990364646258805796127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38463987152861678407728169 28847990364646258805796127)
        ·
          refine ⟨43271985546969388208694191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28847990364646258805796127 43271985546969388208694191)
          ·
            refine ⟨64907978320454082313041287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43271985546969388208694191 64907978320454082313041287)
            ·
              refine ⟨97361967480681123469561931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64907978320454082313041287 97361967480681123469561931)
              ·
                refine ⟨146042951221021685204342897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97361967480681123469561931 146042951221021685204342897)
                ·
                  refine ⟨109532213415766263903257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146042951221021685204342897 109532213415766263903257173)
                  ·
                    refine ⟨1283580625966010905116295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109532213415766263903257173 1283580625966010905116295)
                    ·
                      rfl

theorem cell23_7499293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_7499293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499293 prefixEnd_7499293 := by exact prefixLift 7499293
  have htrace : WordTrace (prefixWord ++ tailWord_7499293) baseStart_7499293 baseEnd_7499293 := by
    simpa [prefixWord, tailWord_7499293, baseEnd_7499293] using wordTrace_append hprefix tailTrace_7499293
  have hstable : (prefixWord ++ tailWord_7499293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499293).length < 2 ^ (prefixWord ++ tailWord_7499293).sum := by decide
  have hdescent : baseEnd_7499293 < baseStart_7499293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499320 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_7499320 : Nat := 118140960795 + 7499320 * 2 ^ 59
def prefixEnd_7499320 : Nat := 4983230072969 + 3 ^ 40 * 7499320 * 2
def baseEnd_7499320 : Nat := 3850755741875704109711261

theorem tailTrace_7499320 : CollatzResearch.WordTrace tailWord_7499320 prefixEnd_7499320 3850755741875704109711261 := by
  unfold tailWord_7499320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136761335595625948366427707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182348447460834597821903609 136761335595625948366427707)
  ·
    refine ⟨205142003393438922549641561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136761335595625948366427707 205142003393438922549641561)
    ·
      refine ⟨153856502545079191912231171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205142003393438922549641561 153856502545079191912231171)
      ·
        refine ⟨230784753817618787868346757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153856502545079191912231171 230784753817618787868346757)
        ·
          refine ⟨43272141340803522725315017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230784753817618787868346757 43272141340803522725315017)
          ·
            refine ⟨32454106005602642043986263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43272141340803522725315017 32454106005602642043986263)
            ·
              refine ⟨48681159008403963065979395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32454106005602642043986263 48681159008403963065979395)
              ·
                refine ⟨73021738512605944598969093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48681159008403963065979395 73021738512605944598969093)
                ·
                  refine ⟨13691575971113614612306705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73021738512605944598969093 13691575971113614612306705)
                  ·
                    refine ⟨10268681978335210959230029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13691575971113614612306705 10268681978335210959230029)
                    ·
                      refine ⟨3850755741875704109711261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268681978335210959230029 3850755741875704109711261)
                      ·
                        rfl

theorem cell23_7499320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_7499320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499320 prefixEnd_7499320 := by exact prefixLift 7499320
  have htrace : WordTrace (prefixWord ++ tailWord_7499320) baseStart_7499320 baseEnd_7499320 := by
    simpa [prefixWord, tailWord_7499320, baseEnd_7499320] using wordTrace_append hprefix tailTrace_7499320
  have hstable : (prefixWord ++ tailWord_7499320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499320).length < 2 ^ (prefixWord ++ tailWord_7499320).sum := by decide
  have hdescent : baseEnd_7499320 < baseStart_7499320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499327 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 3, 4]
def baseStart_7499327 : Nat := 118140960795 + 7499327 * 2 ^ 59
def prefixEnd_7499327 : Nat := 4983230072969 + 3 ^ 40 * 7499327 * 2
def baseEnd_7499327 : Nat := 1283586445413428527441243

theorem tailTrace_7499327 : CollatzResearch.WordTrace tailWord_7499327 prefixEnd_7499327 1283586445413428527441243 := by
  unfold tailWord_7499327
  simp only [CollatzResearch.WordTrace]
  refine ⟨273522926502226536928360235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182348617668151024618906823 273522926502226536928360235)
  ·
    refine ⟨410284389753339805392540353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273522926502226536928360235 410284389753339805392540353)
    ·
      refine ⟨307713292315004854044405265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410284389753339805392540353 307713292315004854044405265)
      ·
        refine ⟨230784969236253640533303949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307713292315004854044405265 230784969236253640533303949)
        ·
          refine ⟨86544363463595115199988981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230784969236253640533303949 86544363463595115199988981)
          ·
            refine ⟨8113534074712042049998967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86544363463595115199988981 8113534074712042049998967)
            ·
              refine ⟨12170301112068063074998451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113534074712042049998967 12170301112068063074998451)
              ·
                refine ⟨18255451668102094612497677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12170301112068063074998451 18255451668102094612497677)
                ·
                  refine ⟨6845794375538285479686629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18255451668102094612497677 6845794375538285479686629)
                  ·
                    refine ⟨1283586445413428527441243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6845794375538285479686629 1283586445413428527441243)
                    ·
                      rfl

theorem cell23_7499327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_7499327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499327 prefixEnd_7499327 := by exact prefixLift 7499327
  have htrace : WordTrace (prefixWord ++ tailWord_7499327) baseStart_7499327 baseEnd_7499327 := by
    simpa [prefixWord, tailWord_7499327, baseEnd_7499327] using wordTrace_append hprefix tailTrace_7499327
  have hstable : (prefixWord ++ tailWord_7499327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499327).length < 2 ^ (prefixWord ++ tailWord_7499327).sum := by decide
  have hdescent : baseEnd_7499327 < baseStart_7499327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499340 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 6]
def baseStart_7499340 : Nat := 118140960795 + 7499340 * 2 ^ 59
def prefixEnd_7499340 : Nat := 4983230072969 + 3 ^ 40 * 7499340 * 2
def baseEnd_7499340 : Nat := 427862890165421559051241

theorem tailTrace_7499340 : CollatzResearch.WordTrace tailWord_7499340 prefixEnd_7499340 427862890165421559051241 := by
  unfold tailWord_7499340
  simp only [CollatzResearch.WordTrace]
  refine ⟨136761700325589720074291737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182348933767452960099055649 136761700325589720074291737)
  ·
    refine ⟨102571275244192290055718803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136761700325589720074291737 102571275244192290055718803)
    ·
      refine ⟨153856912866288435083578205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102571275244192290055718803 153856912866288435083578205)
      ·
        refine ⟨57696342324858163156341827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153856912866288435083578205 57696342324858163156341827)
        ·
          refine ⟨86544513487287244734512741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57696342324858163156341827 86544513487287244734512741)
          ·
            refine ⟨16227096278866358387721139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86544513487287244734512741 16227096278866358387721139)
            ·
              refine ⟨24340644418299537581581709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227096278866358387721139 24340644418299537581581709)
              ·
                refine ⟨9127741656862326593093141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24340644418299537581581709 9127741656862326593093141)
                ·
                  refine ⟨427862890165421559051241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9127741656862326593093141 427862890165421559051241)
                  ·
                    rfl

theorem cell23_7499340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_7499340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499340 prefixEnd_7499340 := by exact prefixLift 7499340
  have htrace : WordTrace (prefixWord ++ tailWord_7499340) baseStart_7499340 baseEnd_7499340 := by
    simpa [prefixWord, tailWord_7499340, baseEnd_7499340] using wordTrace_append hprefix tailTrace_7499340
  have hstable : (prefixWord ++ tailWord_7499340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499340).length < 2 ^ (prefixWord ++ tailWord_7499340).sum := by decide
  have hdescent : baseEnd_7499340 < baseStart_7499340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499383 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 6]
def baseStart_7499383 : Nat := 118140960795 + 7499383 * 2 ^ 59
def prefixEnd_7499383 : Nat := 4983230072969 + 3 ^ 40 * 7499383 * 2
def baseEnd_7499383 : Nat := 1283596030385645787741157

theorem tailTrace_7499383 : CollatzResearch.WordTrace tailWord_7499383 prefixEnd_7499383 1283596030385645787741157 := by
  unfold tailWord_7499383
  simp only [CollatzResearch.WordTrace]
  refine ⟨273524968990023658492398803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182349979326682438994932535 273524968990023658492398803)
  ·
    refine ⟨410287453485035487738598205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273524968990023658492398803 410287453485035487738598205)
    ·
      refine ⟨153857795056888307901974327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410287453485035487738598205 153857795056888307901974327)
      ·
        refine ⟨230786692585332461852961491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153857795056888307901974327 230786692585332461852961491)
        ·
          refine ⟨346180038877998692779442237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230786692585332461852961491 346180038877998692779442237)
          ·
            refine ⟨129817514579249509792290839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346180038877998692779442237 129817514579249509792290839)
            ·
              refine ⟨194726271868874264688436259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129817514579249509792290839 194726271868874264688436259)
              ·
                refine ⟨292089407803311397032654389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194726271868874264688436259 292089407803311397032654389)
                ·
                  refine ⟨27383381981560443471811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292089407803311397032654389 27383381981560443471811349)
                  ·
                    refine ⟨1283596030385645787741157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27383381981560443471811349 1283596030385645787741157)
                    ·
                      rfl

theorem cell23_7499383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_7499383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499383 prefixEnd_7499383 := by exact prefixLift 7499383
  have htrace : WordTrace (prefixWord ++ tailWord_7499383) baseStart_7499383 baseEnd_7499383 := by
    simpa [prefixWord, tailWord_7499383, baseEnd_7499383] using wordTrace_append hprefix tailTrace_7499383
  have hstable : (prefixWord ++ tailWord_7499383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499383).length < 2 ^ (prefixWord ++ tailWord_7499383).sum := by decide
  have hdescent : baseEnd_7499383 < baseStart_7499383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499413 : List Nat := [1, 3, 2, 1, 1, 1, 1, 13]
def baseStart_7499413 : Nat := 118140960795 + 7499413 * 2 ^ 59
def prefixEnd_7499413 : Nat := 4983230072969 + 3 ^ 40 * 7499413 * 2
def baseEnd_7499413 : Nat := 142622351688021194290679

theorem tailTrace_7499413 : CollatzResearch.WordTrace tailWord_7499413 prefixEnd_7499413 142622351688021194290679 := by
  unfold tailWord_7499413
  simp only [CollatzResearch.WordTrace]
  refine ⟨273526063179914973615990893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182350708786609982410660595 273526063179914973615990893)
  ·
    refine ⟨102572273692468115105996585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273526063179914973615990893 102572273692468115105996585)
    ·
      refine ⟨76929205269351086329497439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102572273692468115105996585 76929205269351086329497439)
      ·
        refine ⟨115393807904026629494246159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76929205269351086329497439 115393807904026629494246159)
        ·
          refine ⟨173090711856039944241369239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115393807904026629494246159 173090711856039944241369239)
          ·
            refine ⟨259636067784059916362053859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173090711856039944241369239 259636067784059916362053859)
            ·
              refine ⟨389454101676089874543080789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259636067784059916362053859 389454101676089874543080789)
              ·
                refine ⟨142622351688021194290679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 389454101676089874543080789 142622351688021194290679)
                ·
                  rfl

theorem cell23_7499413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 13].length) (baseStart_7499413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499413 prefixEnd_7499413 := by exact prefixLift 7499413
  have htrace : WordTrace (prefixWord ++ tailWord_7499413) baseStart_7499413 baseEnd_7499413 := by
    simpa [prefixWord, tailWord_7499413, baseEnd_7499413] using wordTrace_append hprefix tailTrace_7499413
  have hstable : (prefixWord ++ tailWord_7499413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499413).length < 2 ^ (prefixWord ++ tailWord_7499413).sum := by decide
  have hdescent : baseEnd_7499413 < baseStart_7499413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499424 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4]
def baseStart_7499424 : Nat := 118140960795 + 7499424 * 2 ^ 59
def prefixEnd_7499424 : Nat := 4983230072969 + 3 ^ 40 * 7499424 * 2
def baseEnd_7499424 : Nat := 3850809143863771702810783

theorem tailTrace_7499424 : CollatzResearch.WordTrace tailWord_7499424 prefixEnd_7499424 3850809143863771702810783 := by
  unfold tailWord_7499424
  simp only [CollatzResearch.WordTrace]
  refine ⟨136763232191437561247320663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182350976255250081663094217 136763232191437561247320663)
  ·
    refine ⟨205144848287156341870980995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136763232191437561247320663 205144848287156341870980995)
    ·
      refine ⟨307717272430734512806471493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205144848287156341870980995 307717272430734512806471493)
      ·
        refine ⟨57696988580762721151213405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307717272430734512806471493 57696988580762721151213405)
        ·
          refine ⟨21636370717786020431705027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57696988580762721151213405 21636370717786020431705027)
          ·
            refine ⟨32454556076679030647557541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21636370717786020431705027 32454556076679030647557541)
            ·
              refine ⟨6085229264377318246417039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32454556076679030647557541 6085229264377318246417039)
              ·
                refine ⟨9127843896565977369625559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085229264377318246417039 9127843896565977369625559)
                ·
                  refine ⟨13691765844848966054438339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127843896565977369625559 13691765844848966054438339)
                  ·
                    refine ⟨20537648767273449081657509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13691765844848966054438339 20537648767273449081657509)
                    ·
                      refine ⟨3850809143863771702810783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20537648767273449081657509 3850809143863771702810783)
                      ·
                        rfl

theorem cell23_7499424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_7499424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499424 prefixEnd_7499424 := by exact prefixLift 7499424
  have htrace : WordTrace (prefixWord ++ tailWord_7499424) baseStart_7499424 baseEnd_7499424 := by
    simpa [prefixWord, tailWord_7499424, baseEnd_7499424] using wordTrace_append hprefix tailTrace_7499424
  have hstable : (prefixWord ++ tailWord_7499424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499424).length < 2 ^ (prefixWord ++ tailWord_7499424).sum := by decide
  have hdescent : baseEnd_7499424 < baseStart_7499424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499427 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 3]
def baseStart_7499427 : Nat := 118140960795 + 7499427 * 2 ^ 59
def prefixEnd_7499427 : Nat := 4983230072969 + 3 ^ 40 * 7499427 * 2
def baseEnd_7499427 : Nat := 3850810684305735191073269

theorem tailTrace_7499427 : CollatzResearch.WordTrace tailWord_7499427 prefixEnd_7499427 3850810684305735191073269 := by
  unfold tailWord_7499427
  simp only [CollatzResearch.WordTrace]
  refine ⟨273526573801864254007000535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182351049201242836004667023 273526573801864254007000535)
  ·
    refine ⟨410289860702796381010500803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273526573801864254007000535 410289860702796381010500803)
    ·
      refine ⟨615434791054194571515751205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410289860702796381010500803 615434791054194571515751205)
      ·
        refine ⟨115394023322661482159203351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615434791054194571515751205 115394023322661482159203351)
        ·
          refine ⟨173091034983992223238805027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115394023322661482159203351 173091034983992223238805027)
          ·
            refine ⟨259636552475988334858207541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173091034983992223238805027 259636552475988334858207541)
            ·
              refine ⟨24340926794623906392956957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259636552475988334858207541 24340926794623906392956957)
              ·
                refine ⟨9127847547983964897358859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24340926794623906392956957 9127847547983964897358859)
                ·
                  refine ⟨13691771321975947346038289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9127847547983964897358859 13691771321975947346038289)
                  ·
                    refine ⟨10268828491481960509528717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13691771321975947346038289 10268828491481960509528717)
                    ·
                      refine ⟨3850810684305735191073269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268828491481960509528717 3850810684305735191073269)
                      ·
                        rfl

theorem cell23_7499427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_7499427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499427 prefixEnd_7499427 := by exact prefixLift 7499427
  have htrace : WordTrace (prefixWord ++ tailWord_7499427) baseStart_7499427 baseEnd_7499427 := by
    simpa [prefixWord, tailWord_7499427, baseEnd_7499427] using wordTrace_append hprefix tailTrace_7499427
  have hstable : (prefixWord ++ tailWord_7499427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499427).length < 2 ^ (prefixWord ++ tailWord_7499427).sum := by decide
  have hdescent : baseEnd_7499427 < baseStart_7499427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499440 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_7499440 : Nat := 118140960795 + 7499440 * 2 ^ 59
def prefixEnd_7499440 : Nat := 4983230072969 + 3 ^ 40 * 7499440 * 2
def baseEnd_7499440 : Nat := 3850817359554243640210709

theorem tailTrace_7499440 : CollatzResearch.WordTrace tailWord_7499440 prefixEnd_7499440 3850817359554243640210709 := by
  unfold tailWord_7499440
  simp only [CollatzResearch.WordTrace]
  refine ⟨136763523975408578613611887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182351365300544771484815849 136763523975408578613611887)
  ·
    refine ⟨205145285963112867920417831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136763523975408578613611887 205145285963112867920417831)
    ·
      refine ⟨307717928944669301880626747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205145285963112867920417831 307717928944669301880626747)
      ·
        refine ⟨461576893417003952820940121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307717928944669301880626747 461576893417003952820940121)
        ·
          refine ⟨346182670062752964615705091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461576893417003952820940121 346182670062752964615705091)
          ·
            refine ⟨519274005094129446923557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346182670062752964615705091 519274005094129446923557637)
            ·
              refine ⟨97363875955149271298167057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519274005094129446923557637 97363875955149271298167057)
              ·
                refine ⟨73022906966361953473625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97363875955149271298167057 73022906966361953473625293)
                ·
                  refine ⟨27383590112385732552609485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73022906966361953473625293 27383590112385732552609485)
                  ·
                    refine ⟨10268846292144649707228557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27383590112385732552609485 10268846292144649707228557)
                    ·
                      refine ⟨3850817359554243640210709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268846292144649707228557 3850817359554243640210709)
                      ·
                        rfl

theorem cell23_7499440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_7499440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499440 prefixEnd_7499440 := by exact prefixLift 7499440
  have htrace : WordTrace (prefixWord ++ tailWord_7499440) baseStart_7499440 baseEnd_7499440 := by
    simpa [prefixWord, tailWord_7499440, baseEnd_7499440] using wordTrace_append hprefix tailTrace_7499440
  have hstable : (prefixWord ++ tailWord_7499440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499440).length < 2 ^ (prefixWord ++ tailWord_7499440).sum := by decide
  have hdescent : baseEnd_7499440 < baseStart_7499440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499454 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_7499454 : Nat := 118140960795 + 7499454 * 2 ^ 59
def prefixEnd_7499454 : Nat := 4983230072969 + 3 ^ 40 * 7499454 * 2
def baseEnd_7499454 : Nat := 3850824548283406585435645

theorem tailTrace_7499454 : CollatzResearch.WordTrace tailWord_7499454 prefixEnd_7499454 3850824548283406585435645 := by
  unfold tailWord_7499454
  simp only [CollatzResearch.WordTrace]
  refine ⟨34190944821595804702279177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182351705715177625078822277 34190944821595804702279177)
  ·
    refine ⟨25643208616196853526709383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34190944821595804702279177 25643208616196853526709383)
    ·
      refine ⟨38464812924295280290064075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25643208616196853526709383 38464812924295280290064075)
      ·
        refine ⟨57697219386442920435096113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38464812924295280290064075 57697219386442920435096113)
        ·
          refine ⟨43272914539832190326322085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57697219386442920435096113 43272914539832190326322085)
          ·
            refine ⟨8113671476218535686185391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43272914539832190326322085 8113671476218535686185391)
            ·
              refine ⟨12170507214327803529278087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8113671476218535686185391 12170507214327803529278087)
              ·
                refine ⟨18255760821491705293917131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12170507214327803529278087 18255760821491705293917131)
                ·
                  refine ⟨27383641232237557940875697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18255760821491705293917131 27383641232237557940875697)
                  ·
                    refine ⟨20537730924178168455656773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27383641232237557940875697 20537730924178168455656773)
                    ·
                      refine ⟨3850824548283406585435645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20537730924178168455656773 3850824548283406585435645)
                      ·
                        rfl

theorem cell23_7499454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_7499454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499454 prefixEnd_7499454 := by exact prefixLift 7499454
  have htrace : WordTrace (prefixWord ++ tailWord_7499454) baseStart_7499454 baseEnd_7499454 := by
    simpa [prefixWord, tailWord_7499454, baseEnd_7499454] using wordTrace_append hprefix tailTrace_7499454
  have hstable : (prefixWord ++ tailWord_7499454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499454).length < 2 ^ (prefixWord ++ tailWord_7499454).sum := by decide
  have hdescent : baseEnd_7499454 < baseStart_7499454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499467 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 3, 3, 2]
def baseStart_7499467 : Nat := 118140960795 + 7499467 * 2 ^ 59
def prefixEnd_7499467 : Nat := 4983230072969 + 3 ^ 40 * 7499467 * 2
def baseEnd_7499467 : Nat := 3850831223531915034573085

theorem tailTrace_7499467 : CollatzResearch.WordTrace tailWord_7499467 prefixEnd_7499467 3850831223531915034573085 := by
  unfold tailWord_7499467
  simp only [CollatzResearch.WordTrace]
  refine ⟨273528032721719340838456655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182352021814479560558971103 273528032721719340838456655)
  ·
    refine ⟨410292049082579011257684983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273528032721719340838456655 410292049082579011257684983)
    ·
      refine ⟨615438073623868516886527475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410292049082579011257684983 615438073623868516886527475)
      ·
        refine ⟨923157110435802775329791213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615438073623868516886527475 923157110435802775329791213)
        ·
          refine ⟨346183916413426040748671705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 923157110435802775329791213 346183916413426040748671705)
          ·
            refine ⟨259637937310069530561503779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346183916413426040748671705 259637937310069530561503779)
            ·
              refine ⟨389456905965104295842255669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259637937310069530561503779 389456905965104295842255669)
              ·
                refine ⟨36511584934228527735211469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389456905965104295842255669 36511584934228527735211469)
                ·
                  refine ⟨13691844350335697900704301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36511584934228527735211469 13691844350335697900704301)
                  ·
                    refine ⟨5134441631375886712764113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13691844350335697900704301 5134441631375886712764113)
                    ·
                      refine ⟨3850831223531915034573085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134441631375886712764113 3850831223531915034573085)
                      ·
                        rfl

theorem cell23_7499467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3, 2].length) (baseStart_7499467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499467 prefixEnd_7499467 := by exact prefixLift 7499467
  have htrace : WordTrace (prefixWord ++ tailWord_7499467) baseStart_7499467 baseEnd_7499467 := by
    simpa [prefixWord, tailWord_7499467, baseEnd_7499467] using wordTrace_append hprefix tailTrace_7499467
  have hstable : (prefixWord ++ tailWord_7499467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499467).length < 2 ^ (prefixWord ++ tailWord_7499467).sum := by decide
  have hdescent : baseEnd_7499467 < baseStart_7499467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499470 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7499470 : Nat := 118140960795 + 7499470 * 2 ^ 59
def prefixEnd_7499470 : Nat := 4983230072969 + 3 ^ 40 * 7499470 * 2
def baseEnd_7499470 : Nat := 3850832763973878522835571

theorem tailTrace_7499470 : CollatzResearch.WordTrace tailWord_7499470 prefixEnd_7499470 3850832763973878522835571 := by
  unfold tailWord_7499470
  simp only [CollatzResearch.WordTrace]
  refine ⟨34191017767588559043851983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182352094760472314900543909 34191017767588559043851983)
  ·
    refine ⟨51286526651382838565777975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34191017767588559043851983 51286526651382838565777975)
    ·
      refine ⟨76929789977074257848666963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51286526651382838565777975 76929789977074257848666963)
      ·
        refine ⟨115394684965611386773000445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76929789977074257848666963 115394684965611386773000445)
        ·
          refine ⟨43273006862104270039875167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115394684965611386773000445 43273006862104270039875167)
          ·
            refine ⟨64909510293156405059812751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43273006862104270039875167 64909510293156405059812751)
            ·
              refine ⟨97364265439734607589719127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64909510293156405059812751 97364265439734607589719127)
              ·
                refine ⟨146046398159601911384578691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97364265439734607589719127 146046398159601911384578691)
                ·
                  refine ⟨219069597239402867076868037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146046398159601911384578691 219069597239402867076868037)
                  ·
                    refine ⟨41075549482388037576912757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219069597239402867076868037 41075549482388037576912757)
                    ·
                      refine ⟨3850832763973878522835571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41075549482388037576912757 3850832763973878522835571)
                      ·
                        rfl

theorem cell23_7499470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7499470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499470 prefixEnd_7499470 := by exact prefixLift 7499470
  have htrace : WordTrace (prefixWord ++ tailWord_7499470) baseStart_7499470 baseEnd_7499470 := by
    simpa [prefixWord, tailWord_7499470, baseEnd_7499470] using wordTrace_append hprefix tailTrace_7499470
  have hstable : (prefixWord ++ tailWord_7499470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499470).length < 2 ^ (prefixWord ++ tailWord_7499470).sum := by decide
  have hdescent : baseEnd_7499470 < baseStart_7499470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499474 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7499474 : Nat := 118140960795 + 7499474 * 2 ^ 59
def prefixEnd_7499474 : Nat := 4983230072969 + 3 ^ 40 * 7499474 * 2
def baseEnd_7499474 : Nat := 3850834817896496507185553

theorem tailTrace_7499474 : CollatzResearch.WordTrace tailWord_7499474 prefixEnd_7499474 3850834817896496507185553 := by
  unfold tailWord_7499474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68382072008173495258490369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182352192021795987355974317 68382072008173495258490369)
  ·
    refine ⟨51286554006130121443867777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68382072008173495258490369 51286554006130121443867777)
    ·
      refine ⟨38464915504597591082900833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51286554006130121443867777 38464915504597591082900833)
      ·
        refine ⟨28848686628448193312175625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38464915504597591082900833 28848686628448193312175625)
        ·
          refine ⟨21636514971336144984131719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28848686628448193312175625 21636514971336144984131719)
          ·
            refine ⟨32454772457004217476197579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21636514971336144984131719 32454772457004217476197579)
            ·
              refine ⟨48682158685506326214296369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32454772457004217476197579 48682158685506326214296369)
              ·
                refine ⟨36511619014129744660722277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48682158685506326214296369 36511619014129744660722277)
                ·
                  refine ⟨6845928565149327123885427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36511619014129744660722277 6845928565149327123885427)
                  ·
                    refine ⟨10268892847723990685828141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6845928565149327123885427 10268892847723990685828141)
                    ·
                      refine ⟨3850834817896496507185553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10268892847723990685828141 3850834817896496507185553)
                      ·
                        rfl

theorem cell23_7499474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7499474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499474 prefixEnd_7499474 := by exact prefixLift 7499474
  have htrace : WordTrace (prefixWord ++ tailWord_7499474) baseStart_7499474 baseEnd_7499474 := by
    simpa [prefixWord, tailWord_7499474, baseEnd_7499474] using wordTrace_append hprefix tailTrace_7499474
  have hstable : (prefixWord ++ tailWord_7499474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499474).length < 2 ^ (prefixWord ++ tailWord_7499474).sum := by decide
  have hdescent : baseEnd_7499474 < baseStart_7499474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499537 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 5]
def baseStart_7499537 : Nat := 118140960795 + 7499537 * 2 ^ 59
def prefixEnd_7499537 : Nat := 4983230072969 + 3 ^ 40 * 7499537 * 2
def baseEnd_7499537 : Nat := 427874129686414417855307

theorem tailTrace_7499537 : CollatzResearch.WordTrace tailWord_7499537 prefixEnd_7499537 427874129686414417855307 := by
  unfold tailWord_7499537
  simp only [CollatzResearch.WordTrace]
  refine ⟨273530585831465742793504865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182353723887643828529003243 273530585831465742793504865)
  ·
    refine ⟨205147939373599307095128649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273530585831465742793504865 205147939373599307095128649)
    ·
      refine ⟨153860954530199480321346487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205147939373599307095128649 153860954530199480321346487)
      ·
        refine ⟨230791431795299220482019731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153860954530199480321346487 230791431795299220482019731)
        ·
          refine ⟨346187147692948830723029597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230791431795299220482019731 346187147692948830723029597)
          ·
            refine ⟨129820180384855811521136099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346187147692948830723029597 129820180384855811521136099)
            ·
              refine ⟨194730270577283717281704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129820180384855811521136099 194730270577283717281704149)
              ·
                refine ⟨4563990716655087123789941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194730270577283717281704149 4563990716655087123789941)
                ·
                  refine ⟨427874129686414417855307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4563990716655087123789941 427874129686414417855307)
                  ·
                    rfl

theorem cell23_7499537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 5].length) (baseStart_7499537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499537 prefixEnd_7499537 := by exact prefixLift 7499537
  have htrace : WordTrace (prefixWord ++ tailWord_7499537) baseStart_7499537 baseEnd_7499537 := by
    simpa [prefixWord, tailWord_7499537, baseEnd_7499537] using wordTrace_append hprefix tailTrace_7499537
  have hstable : (prefixWord ++ tailWord_7499537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499537).length < 2 ^ (prefixWord ++ tailWord_7499537).sum := by decide
  have hdescent : baseEnd_7499537 < baseStart_7499537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499554 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_7499554 : Nat := 118140960795 + 7499554 * 2 ^ 59
def prefixEnd_7499554 : Nat := 4983230072969 + 3 ^ 40 * 7499554 * 2
def baseEnd_7499554 : Nat := 427875099594317354909465

theorem tailTrace_7499554 : CollatzResearch.WordTrace tailWord_7499554 prefixEnd_7499554 427875099594317354909465 := by
  unfold tailWord_7499554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68382801468101038674218429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182354137248269436464582477 68382801468101038674218429)
  ·
    refine ⟨25643550550537889502831911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68382801468101038674218429 25643550550537889502831911)
    ·
      refine ⟨38465325825806834254247867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25643550550537889502831911 38465325825806834254247867)
      ·
        refine ⟨57697988738710251381371801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38465325825806834254247867 57697988738710251381371801)
        ·
          refine ⟨43273491554032688536028851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57697988738710251381371801 43273491554032688536028851)
          ·
            refine ⟨64910237331049032804043277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43273491554032688536028851 64910237331049032804043277)
            ·
              refine ⟨24341338999143387301516229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64910237331049032804043277 24341338999143387301516229)
              ·
                refine ⟨4564001062339385119034293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24341338999143387301516229 4564001062339385119034293)
                ·
                  refine ⟨427875099594317354909465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4564001062339385119034293 427875099594317354909465)
                  ·
                    rfl

theorem cell23_7499554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_7499554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499554 prefixEnd_7499554 := by exact prefixLift 7499554
  have htrace : WordTrace (prefixWord ++ tailWord_7499554) baseStart_7499554 baseEnd_7499554 := by
    simpa [prefixWord, tailWord_7499554, baseEnd_7499554] using wordTrace_append hprefix tailTrace_7499554
  have hstable : (prefixWord ++ tailWord_7499554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499554).length < 2 ^ (prefixWord ++ tailWord_7499554).sum := by decide
  have hdescent : baseEnd_7499554 < baseStart_7499554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499587 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_7499587 : Nat := 118140960795 + 7499587 * 2 ^ 59
def prefixEnd_7499587 : Nat := 4983230072969 + 3 ^ 40 * 7499587 * 2
def baseEnd_7499587 : Nat := 3850892841210454565072533

theorem tailTrace_7499587 : CollatzResearch.WordTrace tailWord_7499587 prefixEnd_7499587 3850892841210454565072533 := by
  unfold tailWord_7499587
  simp only [CollatzResearch.WordTrace]
  refine ⟨273532409481284601332825015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182354939654189734221883343 273532409481284601332825015)
  ·
    refine ⟨410298614221926901999237523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273532409481284601332825015 410298614221926901999237523)
    ·
      refine ⟨615447921332890352998856285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410298614221926901999237523 615447921332890352998856285)
      ·
        refine ⟨230792970499833882374571107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615447921332890352998856285 230792970499833882374571107)
        ·
          refine ⟨346189455749750823561856661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230792970499833882374571107 346189455749750823561856661)
          ·
            refine ⟨16227630738269569854462031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 346189455749750823561856661 16227630738269569854462031)
            ·
              refine ⟨24341446107404354781693047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227630738269569854462031 24341446107404354781693047)
              ·
                refine ⟨36512169161106532172539571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24341446107404354781693047 36512169161106532172539571)
                ·
                  refine ⟨54768253741659798258809357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36512169161106532172539571 54768253741659798258809357)
                  ·
                    refine ⟨20538095153122424347053509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54768253741659798258809357 20538095153122424347053509)
                    ·
                      refine ⟨3850892841210454565072533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20538095153122424347053509 3850892841210454565072533)
                      ·
                        rfl

theorem cell23_7499587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_7499587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499587 prefixEnd_7499587 := by exact prefixLift 7499587
  have htrace : WordTrace (prefixWord ++ tailWord_7499587) baseStart_7499587 baseEnd_7499587 := by
    simpa [prefixWord, tailWord_7499587, baseEnd_7499587] using wordTrace_append hprefix tailTrace_7499587
  have hstable : (prefixWord ++ tailWord_7499587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499587).length < 2 ^ (prefixWord ++ tailWord_7499587).sum := by decide
  have hdescent : baseEnd_7499587 < baseStart_7499587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2]
def baseStart_7499664 : Nat := 118140960795 + 7499664 * 2 ^ 59
def prefixEnd_7499664 : Nat := 4983230072969 + 3 ^ 40 * 7499664 * 2
def baseEnd_7499664 : Nat := 3850932379220850763809679

theorem tailTrace_7499664 : CollatzResearch.WordTrace tailWord_7499664 prefixEnd_7499664 3850932379220850763809679 := by
  unfold tailWord_7499664
  simp only [CollatzResearch.WordTrace]
  refine ⟨136767608951002821741689023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182356811934670428988918697 136767608951002821741689023)
  ·
    refine ⟨205151413426504232612533535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136767608951002821741689023 205151413426504232612533535)
    ·
      refine ⟨307727120139756348918800303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205151413426504232612533535 307727120139756348918800303)
      ·
        refine ⟨461590680209634523378200455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307727120139756348918800303 461590680209634523378200455)
        ·
          refine ⟨692386020314451785067300683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461590680209634523378200455 692386020314451785067300683)
          ·
            refine ⟨1038579030471677677600951025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692386020314451785067300683 1038579030471677677600951025)
            ·
              refine ⟨778934272853758258200713269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038579030471677677600951025 778934272853758258200713269)
              ·
                refine ⟨73025088080039836706316869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778934272853758258200713269 73025088080039836706316869)
                ·
                  refine ⟨13692204015007469382434413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73025088080039836706316869 13692204015007469382434413)
                  ·
                    refine ⟨5134576505627801018412905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13692204015007469382434413 5134576505627801018412905)
                    ·
                      refine ⟨3850932379220850763809679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134576505627801018412905 3850932379220850763809679)
                      ·
                        rfl

theorem cell23_7499664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2].length) (baseStart_7499664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499664 prefixEnd_7499664 := by exact prefixLift 7499664
  have htrace : WordTrace (prefixWord ++ tailWord_7499664) baseStart_7499664 baseEnd_7499664 := by
    simpa [prefixWord, tailWord_7499664, baseEnd_7499664] using wordTrace_append hprefix tailTrace_7499664
  have hstable : (prefixWord ++ tailWord_7499664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499664).length < 2 ^ (prefixWord ++ tailWord_7499664).sum := by decide
  have hdescent : baseEnd_7499664 < baseStart_7499664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499671 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_7499671 : Nat := 118140960795 + 7499671 * 2 ^ 59
def prefixEnd_7499671 : Nat := 4983230072969 + 3 ^ 40 * 7499671 * 2
def baseEnd_7499671 : Nat := 3850935973585432236422147

theorem tailTrace_7499671 : CollatzResearch.WordTrace tailWord_7499671 prefixEnd_7499671 3850935973585432236422147 := by
  unfold tailWord_7499671
  simp only [CollatzResearch.WordTrace]
  refine ⟨273535473212980283678882867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182356982141986855785921911 273535473212980283678882867)
  ·
    refine ⟨410303209819470425518324301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273535473212980283678882867 410303209819470425518324301)
    ·
      refine ⟨153863703682301409569371613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410303209819470425518324301 153863703682301409569371613)
      ·
        refine ⟨57698888880863028588514355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153863703682301409569371613 57698888880863028588514355)
        ·
          refine ⟨86548333321294542882771533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57698888880863028588514355 86548333321294542882771533)
          ·
            refine ⟨32455624995485453581039325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86548333321294542882771533 32455624995485453581039325)
            ·
              refine ⟨12170859373307045092889747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32455624995485453581039325 12170859373307045092889747)
              ·
                refine ⟨18256289059960567639334621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12170859373307045092889747 18256289059960567639334621)
                ·
                  refine ⟨6846108397485212864750483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18256289059960567639334621 6846108397485212864750483)
                  ·
                    refine ⟨10269162596227819297125725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846108397485212864750483 10269162596227819297125725)
                    ·
                      refine ⟨3850935973585432236422147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269162596227819297125725 3850935973585432236422147)
                      ·
                        rfl

theorem cell23_7499671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_7499671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499671 prefixEnd_7499671 := by exact prefixLift 7499671
  have htrace : WordTrace (prefixWord ++ tailWord_7499671) baseStart_7499671 baseEnd_7499671 := by
    simpa [prefixWord, tailWord_7499671, baseEnd_7499671] using wordTrace_append hprefix tailTrace_7499671
  have hstable : (prefixWord ++ tailWord_7499671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499671).length < 2 ^ (prefixWord ++ tailWord_7499671).sum := by decide
  have hdescent : baseEnd_7499671 < baseStart_7499671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499678 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7499678 : Nat := 118140960795 + 7499678 * 2 ^ 59
def prefixEnd_7499678 : Nat := 4983230072969 + 3 ^ 40 * 7499678 * 2
def baseEnd_7499678 : Nat := 427882174216668189892735

theorem tailTrace_7499678 : CollatzResearch.WordTrace tailWord_7499678 prefixEnd_7499678 427882174216668189892735 := by
  unfold tailWord_7499678
  simp only [CollatzResearch.WordTrace]
  refine ⟨34191966065494365484298461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182357152349303282582925125 34191966065494365484298461)
  ·
    refine ⟨12821987274560387056611923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34191966065494365484298461 12821987274560387056611923)
    ·
      refine ⟨19232980911840580584917885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821987274560387056611923 19232980911840580584917885)
      ·
        refine ⟨7212367841940217719344207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19232980911840580584917885 7212367841940217719344207)
        ·
          refine ⟨10818551762910326579016311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212367841940217719344207 10818551762910326579016311)
          ·
            refine ⟨16227827644365489868524467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818551762910326579016311 16227827644365489868524467)
            ·
              refine ⟨24341741466548234802786701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16227827644365489868524467 24341741466548234802786701)
              ·
                refine ⟨9128153049955588051045013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24341741466548234802786701 9128153049955588051045013)
                ·
                  refine ⟨427882174216668189892735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9128153049955588051045013 427882174216668189892735)
                  ·
                    rfl

theorem cell23_7499678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7499678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499678 prefixEnd_7499678 := by exact prefixLift 7499678
  have htrace : WordTrace (prefixWord ++ tailWord_7499678) baseStart_7499678 baseEnd_7499678 := by
    simpa [prefixWord, tailWord_7499678, baseEnd_7499678] using wordTrace_append hprefix tailTrace_7499678
  have hstable : (prefixWord ++ tailWord_7499678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499678).length < 2 ^ (prefixWord ++ tailWord_7499678).sum := by decide
  have hdescent : baseEnd_7499678 < baseStart_7499678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499707 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_7499707 : Nat := 118140960795 + 7499707 * 2 ^ 59
def prefixEnd_7499707 : Nat := 4983230072969 + 3 ^ 40 * 7499707 * 2
def baseEnd_7499707 : Nat := 3850954458888994095571981

theorem tailTrace_7499707 : CollatzResearch.WordTrace tailWord_7499707 prefixEnd_7499707 3850954458888994095571981 := by
  unfold tailWord_7499707
  simp only [CollatzResearch.WordTrace]
  refine ⟨273536786240849861827193375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182357857493899907884795583 273536786240849861827193375)
  ·
    refine ⟨410305179361274792740790063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273536786240849861827193375 410305179361274792740790063)
    ·
      refine ⟨615457769041912189111185095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410305179361274792740790063 615457769041912189111185095)
      ·
        refine ⟨923186653562868283666777643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615457769041912189111185095 923186653562868283666777643)
        ·
          refine ⟨1384779980344302425500166465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923186653562868283666777643 1384779980344302425500166465)
          ·
            refine ⟨1038584985258226819125124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1384779980344302425500166465 1038584985258226819125124849)
            ·
              refine ⟨778938738943670114343843637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038584985258226819125124849 778938738943670114343843637)
              ·
                refine ⟨73025506775969073219735341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 778938738943670114343843637 73025506775969073219735341)
                ·
                  refine ⟨27384565040988402457400753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73025506775969073219735341 27384565040988402457400753)
                  ·
                    refine ⟨20538423780741301843050565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27384565040988402457400753 20538423780741301843050565)
                    ·
                      refine ⟨3850954458888994095571981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20538423780741301843050565 3850954458888994095571981)
                      ·
                        rfl

theorem cell23_7499707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_7499707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499707 prefixEnd_7499707 := by exact prefixLift 7499707
  have htrace : WordTrace (prefixWord ++ tailWord_7499707) baseStart_7499707 baseEnd_7499707 := by
    simpa [prefixWord, tailWord_7499707, baseEnd_7499707] using wordTrace_append hprefix tailTrace_7499707
  have hstable : (prefixWord ++ tailWord_7499707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499707).length < 2 ^ (prefixWord ++ tailWord_7499707).sum := by decide
  have hdescent : baseEnd_7499707 < baseStart_7499707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499711 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 1, 1, 4]
def baseStart_7499711 : Nat := 118140960795 + 7499711 * 2 ^ 59
def prefixEnd_7499711 : Nat := 4983230072969 + 3 ^ 40 * 7499711 * 2
def baseEnd_7499711 : Nat := 3850956512811612079921963

theorem tailTrace_7499711 : CollatzResearch.WordTrace tailWord_7499711 prefixEnd_7499711 3850956512811612079921963 := by
  unfold tailWord_7499711
  simp only [CollatzResearch.WordTrace]
  refine ⟨273536932132835370510338987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182357954755223580340225991 273536932132835370510338987)
  ·
    refine ⟨410305398199253055765508481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273536932132835370510338987 410305398199253055765508481)
    ·
      refine ⟨307729048649439791824131361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410305398199253055765508481 307729048649439791824131361)
      ·
        refine ⟨230796786487079843868098521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307729048649439791824131361 230796786487079843868098521)
        ·
          refine ⟨173097589865309882901073891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230796786487079843868098521 173097589865309882901073891)
          ·
            refine ⟨259646384797964824351610837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173097589865309882901073891 259646384797964824351610837)
            ·
              refine ⟨6085462143702300570740879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259646384797964824351610837 6085462143702300570740879)
              ·
                refine ⟨9128193215553450856111319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085462143702300570740879 9128193215553450856111319)
                ·
                  refine ⟨13692289823330176284166979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128193215553450856111319 13692289823330176284166979)
                  ·
                    refine ⟨20538434734995264426250469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13692289823330176284166979 20538434734995264426250469)
                    ·
                      refine ⟨3850956512811612079921963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20538434734995264426250469 3850956512811612079921963)
                      ·
                        rfl

theorem cell23_7499711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_7499711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499711 prefixEnd_7499711 := by exact prefixLift 7499711
  have htrace : WordTrace (prefixWord ++ tailWord_7499711) baseStart_7499711 baseEnd_7499711 := by
    simpa [prefixWord, tailWord_7499711, baseEnd_7499711] using wordTrace_append hprefix tailTrace_7499711
  have hstable : (prefixWord ++ tailWord_7499711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499711).length < 2 ^ (prefixWord ++ tailWord_7499711).sum := by decide
  have hdescent : baseEnd_7499711 < baseStart_7499711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499751 : List Nat := [1, 1, 5, 2, 3, 1, 3, 7]
def baseStart_7499751 : Nat := 118140960795 + 7499751 * 2 ^ 59
def prefixEnd_7499751 : Nat := 4983230072969 + 3 ^ 40 * 7499751 * 2
def baseEnd_7499751 : Nat := 142628779705103404571177

theorem tailTrace_7499751 : CollatzResearch.WordTrace tailWord_7499751 prefixEnd_7499751 142628779705103404571177 := by
  unfold tailWord_7499751
  simp only [CollatzResearch.WordTrace]
  refine ⟨273538391052690457341795107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182358927368460304894530071 273538391052690457341795107)
  ·
    refine ⟨410307586579035686012692661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273538391052690457341795107 410307586579035686012692661)
    ·
      refine ⟨38466336241784595563689937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410307586579035686012692661 38466336241784595563689937)
      ·
        refine ⟨28849752181338446672767453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38466336241784595563689937 28849752181338446672767453)
        ·
          refine ⟨10818657068001917502287795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28849752181338446672767453 10818657068001917502287795)
          ·
            refine ⟨16227985602002876253431693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818657068001917502287795 16227985602002876253431693)
            ·
              refine ⟨6085494600751078595036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16227985602002876253431693 6085494600751078595036885)
              ·
                refine ⟨142628779705103404571177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085494600751078595036885 142628779705103404571177)
                ·
                  rfl

theorem cell23_7499751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 7].length) (baseStart_7499751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499751 prefixEnd_7499751 := by exact prefixLift 7499751
  have htrace : WordTrace (prefixWord ++ tailWord_7499751) baseStart_7499751 baseEnd_7499751 := by
    simpa [prefixWord, tailWord_7499751, baseEnd_7499751] using wordTrace_append hprefix tailTrace_7499751
  have hstable : (prefixWord ++ tailWord_7499751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499751).length < 2 ^ (prefixWord ++ tailWord_7499751).sum := by decide
  have hdescent : baseEnd_7499751 < baseStart_7499751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499782 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7499782 : Nat := 118140960795 + 7499782 * 2 ^ 59
def prefixEnd_7499782 : Nat := 4983230072969 + 3 ^ 40 * 7499782 * 2
def baseEnd_7499782 : Nat := 3850992969938081302134137

theorem tailTrace_7499782 : CollatzResearch.WordTrace tailWord_7499782 prefixEnd_7499782 3850992969938081302134137 := by
  unfold tailWord_7499782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548110053611817176130425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182359681143718766424115733 8548110053611817176130425)
  ·
    refine ⟨6411082540208862882097819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8548110053611817176130425 6411082540208862882097819)
    ·
      refine ⟨9616623810313294323146729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411082540208862882097819 9616623810313294323146729)
      ·
        refine ⟨7212467857734970742360047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9616623810313294323146729 7212467857734970742360047)
        ·
          refine ⟨10818701786602456113540071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212467857734970742360047 10818701786602456113540071)
          ·
            refine ⟨16228052679903684170310107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818701786602456113540071 16228052679903684170310107)
            ·
              refine ⟨24342079019855526255465161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228052679903684170310107 24342079019855526255465161)
              ·
                refine ⟨18256559264891644691598871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342079019855526255465161 18256559264891644691598871)
                ·
                  refine ⟨27384838897337467037398307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18256559264891644691598871 27384838897337467037398307)
                  ·
                    refine ⟨41077258346006200556097461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27384838897337467037398307 41077258346006200556097461)
                    ·
                      refine ⟨3850992969938081302134137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41077258346006200556097461 3850992969938081302134137)
                      ·
                        rfl

theorem cell23_7499782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7499782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499782 prefixEnd_7499782 := by exact prefixLift 7499782
  have htrace : WordTrace (prefixWord ++ tailWord_7499782) baseStart_7499782 baseEnd_7499782 := by
    simpa [prefixWord, tailWord_7499782, baseEnd_7499782] using wordTrace_append hprefix tailTrace_7499782
  have hstable : (prefixWord ++ tailWord_7499782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499782).length < 2 ^ (prefixWord ++ tailWord_7499782).sum := by decide
  have hdescent : baseEnd_7499782 < baseStart_7499782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499789 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7499789 : Nat := 118140960795 + 7499789 * 2 ^ 59
def prefixEnd_7499789 : Nat := 4983230072969 + 3 ^ 40 * 7499789 * 2
def baseEnd_7499789 : Nat := 1283665521434220924915535

theorem tailTrace_7499789 : CollatzResearch.WordTrace tailWord_7499789 prefixEnd_7499789 1283665521434220924915535 := by
  unfold tailWord_7499789
  simp only [CollatzResearch.WordTrace]
  refine ⟨273539777026552789831678421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182359851351035193221118947 273539777026552789831678421)
  ·
    refine ⟨6411088524059831011679963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 273539777026552789831678421 6411088524059831011679963)
    ·
      refine ⟨9616632786089746517519945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411088524059831011679963 9616632786089746517519945)
      ·
        refine ⟨7212474589567309888139959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9616632786089746517519945 7212474589567309888139959)
        ·
          refine ⟨10818711884350964832209939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212474589567309888139959 10818711884350964832209939)
          ·
            refine ⟨16228067826526447248314909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818711884350964832209939 16228067826526447248314909)
            ·
              refine ⟨6085525434947417718118091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16228067826526447248314909 6085525434947417718118091)
              ·
                refine ⟨9128288152421126577177137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6085525434947417718118091 9128288152421126577177137)
                ·
                  refine ⟨6846216114315844932882853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128288152421126577177137 6846216114315844932882853)
                  ·
                    refine ⟨1283665521434220924915535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846216114315844932882853 1283665521434220924915535)
                    ·
                      rfl

theorem cell23_7499789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7499789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499789 prefixEnd_7499789 := by exact prefixLift 7499789
  have htrace : WordTrace (prefixWord ++ tailWord_7499789) baseStart_7499789 baseEnd_7499789 := by
    simpa [prefixWord, tailWord_7499789, baseEnd_7499789] using wordTrace_append hprefix tailTrace_7499789
  have hstable : (prefixWord ++ tailWord_7499789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499789).length < 2 ^ (prefixWord ++ tailWord_7499789).sum := by decide
  have hdescent : baseEnd_7499789 < baseStart_7499789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499805 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_7499805 : Nat := 118140960795 + 7499805 * 2 ^ 59
def prefixEnd_7499805 : Nat := 4983230072969 + 3 ^ 40 * 7499805 * 2
def baseEnd_7499805 : Nat := 3851004779993134712146531

theorem tailTrace_7499805 : CollatzResearch.WordTrace tailWord_7499805 prefixEnd_7499805 3851004779993134712146531 := by
  unfold tailWord_7499805
  simp only [CollatzResearch.WordTrace]
  refine ⟨273540360594494824564260869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182360240396329883042840579 273540360594494824564260869)
  ·
    refine ⟨51288817611467779605798913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273540360594494824564260869 51288817611467779605798913)
    ·
      refine ⟨38466613208600834704349185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51288817611467779605798913 38466613208600834704349185)
      ·
        refine ⟨28849959906450626028261889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38466613208600834704349185 28849959906450626028261889)
        ·
          refine ⟨21637469929837969521196417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28849959906450626028261889 21637469929837969521196417)
          ·
            refine ⟨16228102447378477140897313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21637469929837969521196417 16228102447378477140897313)
            ·
              refine ⟨12171076835533857855672985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16228102447378477140897313 12171076835533857855672985)
              ·
                refine ⟨9128307626650393391754739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12171076835533857855672985 9128307626650393391754739)
                ·
                  refine ⟨13692461439975590087632109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128307626650393391754739 13692461439975590087632109)
                  ·
                    refine ⟨5134673039990846282862041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13692461439975590087632109 5134673039990846282862041)
                    ·
                      refine ⟨3851004779993134712146531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134673039990846282862041 3851004779993134712146531)
                      ·
                        rfl

theorem cell23_7499805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_7499805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499805 prefixEnd_7499805 := by exact prefixLift 7499805
  have htrace : WordTrace (prefixWord ++ tailWord_7499805) baseStart_7499805 baseEnd_7499805 := by
    simpa [prefixWord, tailWord_7499805, baseEnd_7499805] using wordTrace_append hprefix tailTrace_7499805
  have hstable : (prefixWord ++ tailWord_7499805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499805).length < 2 ^ (prefixWord ++ tailWord_7499805).sum := by decide
  have hdescent : baseEnd_7499805 < baseStart_7499805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499841 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 7]
def baseStart_7499841 : Nat := 118140960795 + 7499841 * 2 ^ 59
def prefixEnd_7499841 : Nat := 4983230072969 + 3 ^ 40 * 7499841 * 2
def baseEnd_7499841 : Nat := 427891473921855174588485

theorem tailTrace_7499841 : CollatzResearch.WordTrace tailWord_7499841 prefixEnd_7499841 427891473921855174588485 := by
  unfold tailWord_7499841
  simp only [CollatzResearch.WordTrace]
  refine ⟨273541673622364402712571377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182361115748242935141714251 273541673622364402712571377)
  ·
    refine ⟨205156255216773302034428533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273541673622364402712571377 205156255216773302034428533)
    ·
      refine ⟨19233398926572497065727675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205156255216773302034428533 19233398926572497065727675)
      ·
        refine ⟨28850098389858745598591513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19233398926572497065727675 28850098389858745598591513)
        ·
          refine ⟨21637573792394059198943635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28850098389858745598591513 21637573792394059198943635)
          ·
            refine ⟨32456360688591088798415453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21637573792394059198943635 32456360688591088798415453)
            ·
              refine ⟨12171135258221658299405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32456360688591088798415453 12171135258221658299405795)
              ·
                refine ⟨18256702887332487449108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12171135258221658299405795 18256702887332487449108693)
                ·
                  refine ⟨427891473921855174588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18256702887332487449108693 427891473921855174588485)
                  ·
                    rfl

theorem cell23_7499841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_7499841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499841 prefixEnd_7499841 := by exact prefixLift 7499841
  have htrace : WordTrace (prefixWord ++ tailWord_7499841) baseStart_7499841 baseEnd_7499841 := by
    simpa [prefixWord, tailWord_7499841, baseEnd_7499841] using wordTrace_append hprefix tailTrace_7499841
  have hstable : (prefixWord ++ tailWord_7499841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499841).length < 2 ^ (prefixWord ++ tailWord_7499841).sum := by decide
  have hdescent : baseEnd_7499841 < baseStart_7499841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499904 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_7499904 : Nat := 118140960795 + 7499904 * 2 ^ 59
def prefixEnd_7499904 : Nat := 4983230072969 + 3 ^ 40 * 7499904 * 2
def baseEnd_7499904 : Nat := 3851055614577929824808575

theorem tailTrace_7499904 : CollatzResearch.WordTrace tailWord_7499904 prefixEnd_7499904 3851055614577929824808575 := by
  unfold tailWord_7499904
  simp only [CollatzResearch.WordTrace]
  refine ⟨136771985710568082236057383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182362647614090776314743177 136771985710568082236057383)
  ·
    refine ⟨205157978565852123354086075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136771985710568082236057383 205157978565852123354086075)
    ·
      refine ⟨307736967848778185031129113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205157978565852123354086075 307736967848778185031129113)
      ·
        refine ⟨230802725886583638773346835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307736967848778185031129113 230802725886583638773346835)
        ·
          refine ⟨346204088829875458160020253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230802725886583638773346835 346204088829875458160020253)
          ·
            refine ⟨129826533311203296810007595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346204088829875458160020253 129826533311203296810007595)
            ·
              refine ⟨194739799966804945215011393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129826533311203296810007595 194739799966804945215011393)
              ·
                refine ⟨146054849975103708911258545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194739799966804945215011393 146054849975103708911258545)
                ·
                  refine ⟨109541137481327781683443909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146054849975103708911258545 109541137481327781683443909)
                  ·
                    refine ⟨20538963277748959065645733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109541137481327781683443909 20538963277748959065645733)
                    ·
                      refine ⟨3851055614577929824808575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20538963277748959065645733 3851055614577929824808575)
                      ·
                        rfl

theorem cell23_7499904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_7499904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499904 prefixEnd_7499904 := by exact prefixLift 7499904
  have htrace : WordTrace (prefixWord ++ tailWord_7499904) baseStart_7499904 baseEnd_7499904 := by
    simpa [prefixWord, tailWord_7499904, baseEnd_7499904] using wordTrace_append hprefix tailTrace_7499904
  have hstable : (prefixWord ++ tailWord_7499904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499904).length < 2 ^ (prefixWord ++ tailWord_7499904).sum := by decide
  have hdescent : baseEnd_7499904 < baseStart_7499904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499908 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7499908 : Nat := 118140960795 + 7499908 * 2 ^ 59
def prefixEnd_7499908 : Nat := 4983230072969 + 3 ^ 40 * 7499908 * 2
def baseEnd_7499908 : Nat := 3851057668500547809158557

theorem tailTrace_7499908 : CollatzResearch.WordTrace tailWord_7499908 prefixEnd_7499908 3851057668500547809158557 := by
  unfold tailWord_7499908
  simp only [CollatzResearch.WordTrace]
  refine ⟨136772058656560836577630189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182362744875414448770173585 136772058656560836577630189)
  ·
    refine ⟨51289521996210313716611321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136772058656560836577630189 51289521996210313716611321)
    ·
      refine ⟨38467141497157735287458491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51289521996210313716611321 38467141497157735287458491)
      ·
        refine ⟨57700712245736602931187737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38467141497157735287458491 57700712245736602931187737)
        ·
          refine ⟨43275534184302452198390803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57700712245736602931187737 43275534184302452198390803)
          ·
            refine ⟨64913301276453678297586205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43275534184302452198390803 64913301276453678297586205)
            ·
              refine ⟨24342487978670129361594827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64913301276453678297586205 24342487978670129361594827)
              ·
                refine ⟨36513731968005194042392241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24342487978670129361594827 36513731968005194042392241)
                ·
                  refine ⟨27385298976003895531794181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36513731968005194042392241 27385298976003895531794181)
                  ·
                    refine ⟨5134743558000730412211409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27385298976003895531794181 5134743558000730412211409)
                    ·
                      refine ⟨3851057668500547809158557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134743558000730412211409 3851057668500547809158557)
                      ·
                        rfl

theorem cell23_7499908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7499908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499908 prefixEnd_7499908 := by exact prefixLift 7499908
  have htrace : WordTrace (prefixWord ++ tailWord_7499908) baseStart_7499908 baseEnd_7499908 := by
    simpa [prefixWord, tailWord_7499908, baseEnd_7499908] using wordTrace_append hprefix tailTrace_7499908
  have hstable : (prefixWord ++ tailWord_7499908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499908).length < 2 ^ (prefixWord ++ tailWord_7499908).sum := by decide
  have hdescent : baseEnd_7499908 < baseStart_7499908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499911 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_7499911 : Nat := 118140960795 + 7499911 * 2 ^ 59
def prefixEnd_7499911 : Nat := 4983230072969 + 3 ^ 40 * 7499911 * 2
def baseEnd_7499911 : Nat := 3851059208942511297421043

theorem tailTrace_7499911 : CollatzResearch.WordTrace tailWord_7499911 prefixEnd_7499911 3851059208942511297421043 := by
  unfold tailWord_7499911
  simp only [CollatzResearch.WordTrace]
  refine ⟨273544226732110804667619587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182362817821407203111746391 273544226732110804667619587)
  ·
    refine ⟨410316340098166207001429381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273544226732110804667619587 410316340098166207001429381)
    ·
      refine ⟨76934313768406163812768009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410316340098166207001429381 76934313768406163812768009)
      ·
        refine ⟨57700735326304622859576007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76934313768406163812768009 57700735326304622859576007)
        ·
          refine ⟨86551102989456934289364011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57700735326304622859576007 86551102989456934289364011)
          ·
            refine ⟨129826654484185401434046017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86551102989456934289364011 129826654484185401434046017)
            ·
              refine ⟨97369990863139051075534513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129826654484185401434046017 97369990863139051075534513)
              ·
                refine ⟨73027493147354288306650885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97369990863139051075534513 73027493147354288306650885)
                ·
                  refine ⟨13692654965128929057497041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73027493147354288306650885 13692654965128929057497041)
                  ·
                    refine ⟨10269491223846696793122781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13692654965128929057497041 10269491223846696793122781)
                    ·
                      refine ⟨3851059208942511297421043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269491223846696793122781 3851059208942511297421043)
                      ·
                        rfl

theorem cell23_7499911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_7499911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499911 prefixEnd_7499911 := by exact prefixLift 7499911
  have htrace : WordTrace (prefixWord ++ tailWord_7499911) baseStart_7499911 baseEnd_7499911 := by
    simpa [prefixWord, tailWord_7499911, baseEnd_7499911] using wordTrace_append hprefix tailTrace_7499911
  have hstable : (prefixWord ++ tailWord_7499911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499911).length < 2 ^ (prefixWord ++ tailWord_7499911).sum := by decide
  have hdescent : baseEnd_7499911 < baseStart_7499911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499926 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7499926 : Nat := 118140960795 + 7499926 * 2 ^ 59
def prefixEnd_7499926 : Nat := 4983230072969 + 3 ^ 40 * 7499926 * 2
def baseEnd_7499926 : Nat := 427896323461369859859275

theorem tailTrace_7499926 : CollatzResearch.WordTrace tailWord_7499926 prefixEnd_7499926 427896323461369859859275 := by
  unfold tailWord_7499926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096548364191028889338477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182363182551370974819610421 17096548364191028889338477)
  ·
    refine ⟨6411205636571635833501929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17096548364191028889338477 6411205636571635833501929)
    ·
      refine ⟨4808404227428726875126447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6411205636571635833501929 4808404227428726875126447)
      ·
        refine ⟨7212606341143090312689671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808404227428726875126447 7212606341143090312689671)
        ·
          refine ⟨10818909511714635469034507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212606341143090312689671 10818909511714635469034507)
          ·
            refine ⟨16228364267571953203551761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818909511714635469034507 16228364267571953203551761)
            ·
              refine ⟨12171273200678964902663821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16228364267571953203551761 12171273200678964902663821)
              ·
                refine ⟨4564227450254611838498933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171273200678964902663821 4564227450254611838498933)
                ·
                  refine ⟨427896323461369859859275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4564227450254611838498933 427896323461369859859275)
                  ·
                    rfl

theorem cell23_7499926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7499926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499926 prefixEnd_7499926 := by exact prefixLift 7499926
  have htrace : WordTrace (prefixWord ++ tailWord_7499926) baseStart_7499926 baseEnd_7499926 := by
    simpa [prefixWord, tailWord_7499926, baseEnd_7499926] using wordTrace_append hprefix tailTrace_7499926
  have hstable : (prefixWord ++ tailWord_7499926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499926).length < 2 ^ (prefixWord ++ tailWord_7499926).sum := by decide
  have hdescent : baseEnd_7499926 < baseStart_7499926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499928 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7499928 : Nat := 118140960795 + 7499928 * 2 ^ 59
def prefixEnd_7499928 : Nat := 4983230072969 + 3 ^ 40 * 7499928 * 2
def baseEnd_7499928 : Nat := 3851067938113637730908465

theorem tailTrace_7499928 : CollatzResearch.WordTrace tailWord_7499928 prefixEnd_7499928 3851067938113637730908465 := by
  unfold tailWord_7499928
  simp only [CollatzResearch.WordTrace]
  refine ⟨136772423386524608285494219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182363231182032811047325625 136772423386524608285494219)
  ·
    refine ⟨205158635079786912428241329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136772423386524608285494219 205158635079786912428241329)
    ·
      refine ⟨153868976309840184321180997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205158635079786912428241329 153868976309840184321180997)
      ·
        refine ⟨28850433058095034560221437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153868976309840184321180997 28850433058095034560221437)
        ·
          refine ⟨10818912396785637960083039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28850433058095034560221437 10818912396785637960083039)
          ·
            refine ⟨16228368595178456940124559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818912396785637960083039 16228368595178456940124559)
            ·
              refine ⟨24342552892767685410186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228368595178456940124559 24342552892767685410186839)
              ·
                refine ⟨36513829339151528115280259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24342552892767685410186839 36513829339151528115280259)
                ·
                  refine ⟨54770744008727292172920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36513829339151528115280259 54770744008727292172920389)
                  ·
                    refine ⟨10269514501636367282422573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54770744008727292172920389 10269514501636367282422573)
                    ·
                      refine ⟨3851067938113637730908465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269514501636367282422573 3851067938113637730908465)
                      ·
                        rfl

theorem cell23_7499928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7499928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499928 prefixEnd_7499928 := by exact prefixLift 7499928
  have htrace : WordTrace (prefixWord ++ tailWord_7499928) baseStart_7499928 baseEnd_7499928 := by
    simpa [prefixWord, tailWord_7499928, baseEnd_7499928] using wordTrace_append hprefix tailTrace_7499928
  have hstable : (prefixWord ++ tailWord_7499928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499928).length < 2 ^ (prefixWord ++ tailWord_7499928).sum := by decide
  have hdescent : baseEnd_7499928 < baseStart_7499928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499935 : List Nat := [1, 1, 2, 6, 1, 1, 1, 5, 1, 4]
def baseStart_7499935 : Nat := 118140960795 + 7499935 * 2 ^ 59
def prefixEnd_7499935 : Nat := 4983230072969 + 3 ^ 40 * 7499935 * 2
def baseEnd_7499935 : Nat := 1283690510826073067840311

theorem tailTrace_7499935 : CollatzResearch.WordTrace tailWord_7499935 prefixEnd_7499935 1283690510826073067840311 := by
  unfold tailWord_7499935
  simp only [CollatzResearch.WordTrace]
  refine ⟨273545102084023856766493259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182363401389349237844328839 273545102084023856766493259)
  ·
    refine ⟨410317653126035785149739889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273545102084023856766493259 410317653126035785149739889)
    ·
      refine ⟨307738239844526838862304917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410317653126035785149739889 307738239844526838862304917)
      ·
        refine ⟨14425229992712195571670543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307738239844526838862304917 14425229992712195571670543)
        ·
          refine ⟨21637844989068293357505815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425229992712195571670543 21637844989068293357505815)
          ·
            refine ⟨32456767483602440036258723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21637844989068293357505815 32456767483602440036258723)
            ·
              refine ⟨48685151225403660054388085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32456767483602440036258723 48685151225403660054388085)
              ·
                refine ⟨4564232927381593130098883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48685151225403660054388085 4564232927381593130098883)
                ·
                  refine ⟨6846349391072389695148325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564232927381593130098883 6846349391072389695148325)
                  ·
                    refine ⟨1283690510826073067840311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846349391072389695148325 1283690510826073067840311)
                    ·
                      rfl

theorem cell23_7499935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_7499935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499935 prefixEnd_7499935 := by exact prefixLift 7499935
  have htrace : WordTrace (prefixWord ++ tailWord_7499935) baseStart_7499935 baseEnd_7499935 := by
    simpa [prefixWord, tailWord_7499935, baseEnd_7499935] using wordTrace_append hprefix tailTrace_7499935
  have hstable : (prefixWord ++ tailWord_7499935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499935).length < 2 ^ (prefixWord ++ tailWord_7499935).sum := by decide
  have hdescent : baseEnd_7499935 < baseStart_7499935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
