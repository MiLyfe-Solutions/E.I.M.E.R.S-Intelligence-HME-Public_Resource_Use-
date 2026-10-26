import V185TrunkScan23Chunk1347

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7982810 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_7982810 : Nat := 118140960795 + 7982810 * 2 ^ 59
def prefixEnd_7982810 : Nat := 4983230072969 + 3 ^ 40 * 7982810 * 2
def baseEnd_7982810 : Nat := 455446500390890828095859

theorem tailTrace_7982810 : CollatzResearch.WordTrace tailWord_7982810 prefixEnd_7982810 455446500390890828095859 := by
  unfold tailWord_7982810
  simp only [CollatzResearch.WordTrace]
  refine ⟨72789250052412550062710471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194104666806433466833894589 72789250052412550062710471)
  ·
    refine ⟨109183875078618825094065707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72789250052412550062710471 109183875078618825094065707)
    ·
      refine ⟨163775812617928237641098561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109183875078618825094065707 163775812617928237641098561)
      ·
        refine ⟨122831859463446178230823921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163775812617928237641098561 122831859463446178230823921)
        ·
          refine ⟨92123894597584633673117941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122831859463446178230823921 92123894597584633673117941)
          ·
            refine ⟨8636615118523559406854807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92123894597584633673117941 8636615118523559406854807)
            ·
              refine ⟨12954922677785339110282211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636615118523559406854807 12954922677785339110282211)
              ·
                refine ⟨19432384016678008665423317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954922677785339110282211 19432384016678008665423317)
                ·
                  refine ⟨455446500390890828095859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19432384016678008665423317 455446500390890828095859)
                  ·
                    rfl

theorem cell23_7982810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_7982810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982810 prefixEnd_7982810 := by exact prefixLift 7982810
  have htrace : WordTrace (prefixWord ++ tailWord_7982810) baseStart_7982810 baseEnd_7982810 := by
    simpa [prefixWord, tailWord_7982810, baseEnd_7982810] using wordTrace_append hprefix tailTrace_7982810
  have hstable : (prefixWord ++ tailWord_7982810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982810).length < 2 ^ (prefixWord ++ tailWord_7982810).sum := by decide
  have hdescent : baseEnd_7982810 < baseStart_7982810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982850 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7982850 : Nat := 118140960795 + 7982850 * 2 ^ 59
def prefixEnd_7982850 : Nat := 4983230072969 + 3 ^ 40 * 7982850 * 2
def baseEnd_7982850 : Nat := 4099039042744197296362547

theorem tailTrace_7982850 : CollatzResearch.WordTrace tailWord_7982850 prefixEnd_7982850 4099039042744197296362547 := by
  unfold tailWord_7982850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72789614782376321770574501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194105639419670191388198669 72789614782376321770574501)
  ·
    refine ⟨13648052771695560331982719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72789614782376321770574501 13648052771695560331982719)
    ·
      refine ⟨20472079157543340497974079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648052771695560331982719 20472079157543340497974079)
      ·
        refine ⟨30708118736315010746961119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20472079157543340497974079 30708118736315010746961119)
        ·
          refine ⟨46062178104472516120441679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30708118736315010746961119 46062178104472516120441679)
          ·
            refine ⟨69093267156708774180662519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46062178104472516120441679 69093267156708774180662519)
            ·
              refine ⟨103639900735063161270993779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69093267156708774180662519 103639900735063161270993779)
              ·
                refine ⟨155459851102594741906490669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103639900735063161270993779 155459851102594741906490669)
                ·
                  refine ⟨58297444163473028214934001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155459851102594741906490669 58297444163473028214934001)
                  ·
                    refine ⟨43723083122604771161200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58297444163473028214934001 43723083122604771161200501)
                    ·
                      refine ⟨4099039042744197296362547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43723083122604771161200501 4099039042744197296362547)
                      ·
                        rfl

theorem cell23_7982850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7982850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982850 prefixEnd_7982850 := by exact prefixLift 7982850
  have htrace : WordTrace (prefixWord ++ tailWord_7982850) baseStart_7982850 baseEnd_7982850 := by
    simpa [prefixWord, tailWord_7982850, baseEnd_7982850] using wordTrace_append hprefix tailTrace_7982850
  have hstable : (prefixWord ++ tailWord_7982850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982850).length < 2 ^ (prefixWord ++ tailWord_7982850).sum := by decide
  have hdescent : baseEnd_7982850 < baseStart_7982850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982860 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_7982860 : Nat := 118140960795 + 7982860 * 2 ^ 59
def prefixEnd_7982860 : Nat := 4983230072969 + 3 ^ 40 * 7982860 * 2
def baseEnd_7982860 : Nat := 4099044177550742257237501

theorem tailTrace_7982860 : CollatzResearch.WordTrace tailWord_7982860 prefixEnd_7982860 4099044177550742257237501 := by
  unfold tailWord_7982860
  simp only [CollatzResearch.WordTrace]
  refine ⟨145579411929734529395081017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194105882572979372526774689 145579411929734529395081017)
  ·
    refine ⟨109184558947300897046310763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145579411929734529395081017 109184558947300897046310763)
    ·
      refine ⟨163776838420951345569466145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109184558947300897046310763 163776838420951345569466145)
      ·
        refine ⟨122832628815713509177099609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163776838420951345569466145 122832628815713509177099609)
        ·
          refine ⟨92124471611785131882824707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122832628815713509177099609 92124471611785131882824707)
          ·
            refine ⟨138186707417677697824237061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92124471611785131882824707 138186707417677697824237061)
            ·
              refine ⟨25910007640814568342044449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138186707417677697824237061 25910007640814568342044449)
              ·
                refine ⟨19432505730610926256533337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25910007640814568342044449 19432505730610926256533337)
                ·
                  refine ⟨14574379297958194692400003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19432505730610926256533337 14574379297958194692400003)
                  ·
                    refine ⟨21861568946937292038600005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14574379297958194692400003 21861568946937292038600005)
                    ·
                      refine ⟨4099044177550742257237501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21861568946937292038600005 4099044177550742257237501)
                      ·
                        rfl

theorem cell23_7982860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_7982860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982860 prefixEnd_7982860 := by exact prefixLift 7982860
  have htrace : WordTrace (prefixWord ++ tailWord_7982860) baseStart_7982860 baseEnd_7982860 := by
    simpa [prefixWord, tailWord_7982860, baseEnd_7982860] using wordTrace_append hprefix tailTrace_7982860
  have hstable : (prefixWord ++ tailWord_7982860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982860).length < 2 ^ (prefixWord ++ tailWord_7982860).sum := by decide
  have hdescent : baseEnd_7982860 < baseStart_7982860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982880 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_7982880 : Nat := 118140960795 + 7982880 * 2 ^ 59
def prefixEnd_7982880 : Nat := 4983230072969 + 3 ^ 40 * 7982880 * 2
def baseEnd_7982880 : Nat := 4099054447163832178987409

theorem tailTrace_7982880 : CollatzResearch.WordTrace tailWord_7982880 prefixEnd_7982880 4099054447163832178987409 := by
  unfold tailWord_7982880
  simp only [CollatzResearch.WordTrace]
  refine ⟨145579776659698301102945047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194106368879597734803926729 145579776659698301102945047)
  ·
    refine ⟨218369664989547451654417571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145579776659698301102945047 218369664989547451654417571)
    ·
      refine ⟨327554497484321177481626357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218369664989547451654417571 327554497484321177481626357)
      ·
        refine ⟨30708234139155110388902471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327554497484321177481626357 30708234139155110388902471)
        ·
          refine ⟨46062351208732665583353707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30708234139155110388902471 46062351208732665583353707)
          ·
            refine ⟨69093526813098998375030561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46062351208732665583353707 69093526813098998375030561)
            ·
              refine ⟨51820145109824248781272921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69093526813098998375030561 51820145109824248781272921)
              ·
                refine ⟨38865108832368186585954691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51820145109824248781272921 38865108832368186585954691)
                ·
                  refine ⟨58297663248552279878932037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38865108832368186585954691 58297663248552279878932037)
                  ·
                    refine ⟨10930811859103552477299757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58297663248552279878932037 10930811859103552477299757)
                    ·
                      refine ⟨4099054447163832178987409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930811859103552477299757 4099054447163832178987409)
                      ·
                        rfl

theorem cell23_7982880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_7982880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982880 prefixEnd_7982880 := by exact prefixLift 7982880
  have htrace : WordTrace (prefixWord ++ tailWord_7982880) baseStart_7982880 baseEnd_7982880 := by
    simpa [prefixWord, tailWord_7982880, baseEnd_7982880] using wordTrace_append hprefix tailTrace_7982880
  have hstable : (prefixWord ++ tailWord_7982880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982880).length < 2 ^ (prefixWord ++ tailWord_7982880).sum := by decide
  have hdescent : baseEnd_7982880 < baseStart_7982880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982897 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_7982897 : Nat := 118140960795 + 7982897 * 2 ^ 59
def prefixEnd_7982897 : Nat := 4983230072969 + 3 ^ 40 * 7982897 * 2
def baseEnd_7982897 : Nat := 4099063176334958612474831

theorem tailTrace_7982897 : CollatzResearch.WordTrace tailWord_7982897 prefixEnd_7982897 4099063176334958612474831 := by
  unfold tailWord_7982897
  simp only [CollatzResearch.WordTrace]
  refine ⟨291160173360335014109258945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194106782240223342739505963 291160173360335014109258945)
  ·
    refine ⟨218370130020251260581944209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291160173360335014109258945 218370130020251260581944209)
    ·
      refine ⟨163777597515188445436458157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218370130020251260581944209 163777597515188445436458157)
      ·
        refine ⟨61416599068195667038671809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163777597515188445436458157 61416599068195667038671809)
        ·
          refine ⟨46062449301146750279003857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61416599068195667038671809 46062449301146750279003857)
          ·
            refine ⟨34546836975860062709252893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46062449301146750279003857 34546836975860062709252893)
            ·
              refine ⟨12955063865947523515969835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34546836975860062709252893 12955063865947523515969835)
              ·
                refine ⟨19432595798921285273954753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12955063865947523515969835 19432595798921285273954753)
                ·
                  refine ⟨14574446849190963955466065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19432595798921285273954753 14574446849190963955466065)
                  ·
                    refine ⟨10930835136893222966599549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14574446849190963955466065 10930835136893222966599549)
                    ·
                      refine ⟨4099063176334958612474831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930835136893222966599549 4099063176334958612474831)
                      ·
                        rfl

theorem cell23_7982897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_7982897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982897 prefixEnd_7982897 := by exact prefixLift 7982897
  have htrace : WordTrace (prefixWord ++ tailWord_7982897) baseStart_7982897 baseEnd_7982897 := by
    simpa [prefixWord, tailWord_7982897, baseEnd_7982897] using wordTrace_append hprefix tailTrace_7982897
  have hstable : (prefixWord ++ tailWord_7982897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982897).length < 2 ^ (prefixWord ++ tailWord_7982897).sum := by decide
  have hdescent : baseEnd_7982897 < baseStart_7982897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982904 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 1, 4]
def baseStart_7982904 : Nat := 118140960795 + 7982904 * 2 ^ 59
def prefixEnd_7982904 : Nat := 4983230072969 + 3 ^ 40 * 7982904 * 2
def baseEnd_7982904 : Nat := 1366355590233180028362433

theorem tailTrace_7982904 : CollatzResearch.WordTrace tailWord_7982904 prefixEnd_7982904 1366355590233180028362433 := by
  unfold tailWord_7982904
  simp only [CollatzResearch.WordTrace]
  refine ⟨145580214335654827152381883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194106952447539769536509177 145580214335654827152381883)
  ·
    refine ⟨218370321503482240728572825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145580214335654827152381883 218370321503482240728572825)
    ·
      refine ⟨163777741127611680546429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218370321503482240728572825 163777741127611680546429619)
      ·
        refine ⟨245666611691417520819644429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163777741127611680546429619 245666611691417520819644429)
        ·
          refine ⟨92124979384281570307366661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245666611691417520819644429 92124979384281570307366661)
          ·
            refine ⟨17273433634552794432631249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92124979384281570307366661 17273433634552794432631249)
            ·
              refine ⟨12955075225914595824473437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17273433634552794432631249 12955075225914595824473437)
              ·
                refine ⟨4858153209717973434177539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12955075225914595824473437 4858153209717973434177539)
                ·
                  refine ⟨7287229814576960151266309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858153209717973434177539 7287229814576960151266309)
                  ·
                    refine ⟨1366355590233180028362433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7287229814576960151266309 1366355590233180028362433)
                    ·
                      rfl

theorem cell23_7982904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_7982904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982904 prefixEnd_7982904 := by exact prefixLift 7982904
  have htrace : WordTrace (prefixWord ++ tailWord_7982904) baseStart_7982904 baseEnd_7982904 := by
    simpa [prefixWord, tailWord_7982904, baseEnd_7982904] using wordTrace_append hprefix tailTrace_7982904
  have hstable : (prefixWord ++ tailWord_7982904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982904).length < 2 ^ (prefixWord ++ tailWord_7982904).sum := by decide
  have hdescent : baseEnd_7982904 < baseStart_7982904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982970 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_7982970 : Nat := 118140960795 + 7982970 * 2 ^ 59
def prefixEnd_7982970 : Nat := 4983230072969 + 3 ^ 40 * 7982970 * 2
def baseEnd_7982970 : Nat := 4099100660422736826861995

theorem tailTrace_7982970 : CollatzResearch.WordTrace tailWord_7982970 prefixEnd_7982970 4099100660422736826861995 := by
  unfold tailWord_7982970
  simp only [CollatzResearch.WordTrace]
  refine ⟨72790708972267636894166591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194108557259380365051110909 72790708972267636894166591)
  ·
    refine ⟨109186063458401455341249887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72790708972267636894166591 109186063458401455341249887)
    ·
      refine ⟨163779095187602183011874831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109186063458401455341249887 163779095187602183011874831)
      ·
        refine ⟨245668642781403274517812247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163779095187602183011874831 245668642781403274517812247)
        ·
          refine ⟨368502964172104911776718371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245668642781403274517812247 368502964172104911776718371)
          ·
            refine ⟨552754446258157367665077557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368502964172104911776718371 552754446258157367665077557)
            ·
              refine ⟨51820729336702253218601021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 552754446258157367665077557 51820729336702253218601021)
              ·
                refine ⟨19432773501263344956975383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51820729336702253218601021 19432773501263344956975383)
                ·
                  refine ⟨29149160251895017435463075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19432773501263344956975383 29149160251895017435463075)
                  ·
                    refine ⟨43723740377842526153194613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29149160251895017435463075 43723740377842526153194613)
                    ·
                      refine ⟨4099100660422736826861995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43723740377842526153194613 4099100660422736826861995)
                      ·
                        rfl

theorem cell23_7982970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_7982970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982970 prefixEnd_7982970 := by exact prefixLift 7982970
  have htrace : WordTrace (prefixWord ++ tailWord_7982970) baseStart_7982970 baseEnd_7982970 := by
    simpa [prefixWord, tailWord_7982970, baseEnd_7982970] using wordTrace_append hprefix tailTrace_7982970
  have hstable : (prefixWord ++ tailWord_7982970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982970).length < 2 ^ (prefixWord ++ tailWord_7982970).sum := by decide
  have hdescent : baseEnd_7982970 < baseStart_7982970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7982980 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7982980 : Nat := 118140960795 + 7982980 * 2 ^ 59
def prefixEnd_7982980 : Nat := 4983230072969 + 3 ^ 40 * 7982980 * 2
def baseEnd_7982980 : Nat := 4099105795229281787736949

theorem tailTrace_7982980 : CollatzResearch.WordTrace tailWord_7982980 prefixEnd_7982980 4099105795229281787736949 := by
  unfold tailWord_7982980
  simp only [CollatzResearch.WordTrace]
  refine ⟨145581600309517159642265197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194108800412689546189686929 145581600309517159642265197)
  ·
    refine ⟨54593100116068934865849449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145581600309517159642265197 54593100116068934865849449)
    ·
      refine ⟨40944825087051701149387087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54593100116068934865849449 40944825087051701149387087)
      ·
        refine ⟨61417237630577551724080631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40944825087051701149387087 61417237630577551724080631)
        ·
          refine ⟨92125856445866327586120947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61417237630577551724080631 92125856445866327586120947)
          ·
            refine ⟨138188784668799491379181421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92125856445866327586120947 138188784668799491379181421)
            ·
              refine ⟨51820794250799809267193033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138188784668799491379181421 51820794250799809267193033)
              ·
                refine ⟨38865595688099856950394775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51820794250799809267193033 38865595688099856950394775)
                ·
                  refine ⟨58298393532149785425592163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38865595688099856950394775 58298393532149785425592163)
                  ·
                    refine ⟨87447590298224678138388245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58298393532149785425592163 87447590298224678138388245)
                    ·
                      refine ⟨4099105795229281787736949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87447590298224678138388245 4099105795229281787736949)
                      ·
                        rfl

theorem cell23_7982980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7982980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7982980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7982980 prefixEnd_7982980 := by exact prefixLift 7982980
  have htrace : WordTrace (prefixWord ++ tailWord_7982980) baseStart_7982980 baseEnd_7982980 := by
    simpa [prefixWord, tailWord_7982980, baseEnd_7982980] using wordTrace_append hprefix tailTrace_7982980
  have hstable : (prefixWord ++ tailWord_7982980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7982980).length < 2 ^ (prefixWord ++ tailWord_7982980).sum := by decide
  have hdescent : baseEnd_7982980 < baseStart_7982980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7982980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983004 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7983004 : Nat := 118140960795 + 7983004 * 2 ^ 59
def prefixEnd_7983004 : Nat := 4983230072969 + 3 ^ 40 * 7983004 * 2
def baseEnd_7983004 : Nat := 4099118118764989693836839

theorem tailTrace_7983004 : CollatzResearch.WordTrace tailWord_7983004 prefixEnd_7983004 4099118118764989693836839 := by
  unfold tailWord_7983004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145582037985473685691702033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194109383980631580922269377 145582037985473685691702033)
  ·
    refine ⟨109186528489105264268776525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145582037985473685691702033 109186528489105264268776525)
    ·
      refine ⟨40944948183414474100791197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109186528489105264268776525 40944948183414474100791197)
      ·
        refine ⟨15354355568780427787796699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40944948183414474100791197 15354355568780427787796699)
        ·
          refine ⟨23031533353170641681695049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354355568780427787796699 23031533353170641681695049)
          ·
            refine ⟨17273650014877981261271287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23031533353170641681695049 17273650014877981261271287)
            ·
              refine ⟨25910475022316971891906931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17273650014877981261271287 25910475022316971891906931)
              ·
                refine ⟨38865712533475457837860397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25910475022316971891906931 38865712533475457837860397)
                ·
                  refine ⟨14574642200053296689197649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38865712533475457837860397 14574642200053296689197649)
                  ·
                    refine ⟨10930981650039972516898237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14574642200053296689197649 10930981650039972516898237)
                    ·
                      refine ⟨4099118118764989693836839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930981650039972516898237 4099118118764989693836839)
                      ·
                        rfl

theorem cell23_7983004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7983004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983004 prefixEnd_7983004 := by exact prefixLift 7983004
  have htrace : WordTrace (prefixWord ++ tailWord_7983004) baseStart_7983004 baseEnd_7983004 := by
    simpa [prefixWord, tailWord_7983004, baseEnd_7983004] using wordTrace_append hprefix tailTrace_7983004
  have hstable : (prefixWord ++ tailWord_7983004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983004).length < 2 ^ (prefixWord ++ tailWord_7983004).sum := by decide
  have hdescent : baseEnd_7983004 < baseStart_7983004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983017 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_7983017 : Nat := 118140960795 + 7983017 * 2 ^ 59
def prefixEnd_7983017 : Nat := 4983230072969 + 3 ^ 40 * 7983017 * 2
def baseEnd_7983017 : Nat := 4099124794013498142974279

theorem tailTrace_7983017 : CollatzResearch.WordTrace tailWord_7983017 prefixEnd_7983017 4099124794013498142974279 := by
  unfold tailWord_7983017
  simp only [CollatzResearch.WordTrace]
  refine ⟨291164550119900274603627305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194109700079933516402418203 291164550119900274603627305)
  ·
    refine ⟨218373412589925205952720479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291164550119900274603627305 218373412589925205952720479)
    ·
      refine ⟨327560118884887808929080719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218373412589925205952720479 327560118884887808929080719)
      ·
        refine ⟨491340178327331713393621079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327560118884887808929080719 491340178327331713393621079)
        ·
          refine ⟨737010267490997570090431619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491340178327331713393621079 737010267490997570090431619)
          ·
            refine ⟨1105515401236496355135647429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737010267490997570090431619 1105515401236496355135647429)
            ·
              refine ⟨207284137731843066587933893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1105515401236496355135647429 207284137731843066587933893)
              ·
                refine ⟨38865775824720574985237605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207284137731843066587933893 38865775824720574985237605)
                ·
                  refine ⟨7287332967135107809732051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38865775824720574985237605 7287332967135107809732051)
                  ·
                    refine ⟨10930999450702661714598077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287332967135107809732051 10930999450702661714598077)
                    ·
                      refine ⟨4099124794013498142974279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10930999450702661714598077 4099124794013498142974279)
                      ·
                        rfl

theorem cell23_7983017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_7983017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983017 prefixEnd_7983017 := by exact prefixLift 7983017
  have htrace : WordTrace (prefixWord ++ tailWord_7983017) baseStart_7983017 baseEnd_7983017 := by
    simpa [prefixWord, tailWord_7983017, baseEnd_7983017] using wordTrace_append hprefix tailTrace_7983017
  have hstable : (prefixWord ++ tailWord_7983017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983017).length < 2 ^ (prefixWord ++ tailWord_7983017).sum := by decide
  have hdescent : baseEnd_7983017 < baseStart_7983017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983028 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7983028 : Nat := 118140960795 + 7983028 * 2 ^ 59
def prefixEnd_7983028 : Nat := 4983230072969 + 3 ^ 40 * 7983028 * 2
def baseEnd_7983028 : Nat := 1366376814100232533312243

theorem tailTrace_7983028 : CollatzResearch.WordTrace tailWord_7983028 prefixEnd_7983028 1366376814100232533312243 := by
  unfold tailWord_7983028
  simp only [CollatzResearch.WordTrace]
  refine ⟨145582475661430211741138869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194109967548573615654851825 145582475661430211741138869)
  ·
    refine ⟨13648357093259082350731769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145582475661430211741138869 13648357093259082350731769)
    ·
      refine ⟨10236267819944311763048827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13648357093259082350731769 10236267819944311763048827)
      ·
        refine ⟨15354401729916467644573241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10236267819944311763048827 15354401729916467644573241)
        ·
          refine ⟨11515801297437350733429931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15354401729916467644573241 11515801297437350733429931)
          ·
            refine ⟨17273701946156026100144897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11515801297437350733429931 17273701946156026100144897)
            ·
              refine ⟨12955276459617019575108673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17273701946156026100144897 12955276459617019575108673)
              ·
                refine ⟨9716457344712764681331505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12955276459617019575108673 9716457344712764681331505)
                ·
                  refine ⟨7287343008534573510998629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9716457344712764681331505 7287343008534573510998629)
                  ·
                    refine ⟨1366376814100232533312243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7287343008534573510998629 1366376814100232533312243)
                    ·
                      rfl

theorem cell23_7983028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7983028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983028 prefixEnd_7983028 := by exact prefixLift 7983028
  have htrace : WordTrace (prefixWord ++ tailWord_7983028) baseStart_7983028 baseEnd_7983028 := by
    simpa [prefixWord, tailWord_7983028, baseEnd_7983028] using wordTrace_append hprefix tailTrace_7983028
  have hstable : (prefixWord ++ tailWord_7983028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983028).length < 2 ^ (prefixWord ++ tailWord_7983028).sum := by decide
  have hdescent : baseEnd_7983028 < baseStart_7983028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983040 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_7983040 : Nat := 118140960795 + 7983040 * 2 ^ 59
def prefixEnd_7983040 : Nat := 4983230072969 + 3 ^ 40 * 7983040 * 2
def baseEnd_7983040 : Nat := 4099136604068551552986673

theorem tailTrace_7983040 : CollatzResearch.WordTrace tailWord_7983040 prefixEnd_7983040 4099136604068551552986673 := by
  unfold tailWord_7983040
  simp only [CollatzResearch.WordTrace]
  refine ⟨145582694499408474765857287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194110259332544633021143049 145582694499408474765857287)
  ·
    refine ⟨218374041749112712148785931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145582694499408474765857287 218374041749112712148785931)
    ·
      refine ⟨327561062623669068223178897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218374041749112712148785931 327561062623669068223178897)
      ·
        refine ⟨245670796967751801167384173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327561062623669068223178897 245670796967751801167384173)
        ·
          refine ⟨92126548862906925437769065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245670796967751801167384173 92126548862906925437769065)
          ·
            refine ⟨69094911647180194078326799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92126548862906925437769065 69094911647180194078326799)
            ·
              refine ⟨103642367470770291117490199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69094911647180194078326799 103642367470770291117490199)
              ·
                refine ⟨155463551206155436676235299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103642367470770291117490199 155463551206155436676235299)
                ·
                  refine ⟨233195326809233155014352949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155463551206155436676235299 233195326809233155014352949)
                  ·
                    refine ⟨21862061888365608282595589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233195326809233155014352949 21862061888365608282595589)
                    ·
                      refine ⟨4099136604068551552986673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21862061888365608282595589 4099136604068551552986673)
                      ·
                        rfl

theorem cell23_7983040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_7983040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983040 prefixEnd_7983040 := by exact prefixLift 7983040
  have htrace : WordTrace (prefixWord ++ tailWord_7983040) baseStart_7983040 baseEnd_7983040 := by
    simpa [prefixWord, tailWord_7983040, baseEnd_7983040] using wordTrace_append hprefix tailTrace_7983040
  have hstable : (prefixWord ++ tailWord_7983040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983040).length < 2 ^ (prefixWord ++ tailWord_7983040).sum := by decide
  have hdescent : baseEnd_7983040 < baseStart_7983040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983050 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_7983050 : Nat := 118140960795 + 7983050 * 2 ^ 59
def prefixEnd_7983050 : Nat := 4983230072969 + 3 ^ 40 * 7983050 * 2
def baseEnd_7983050 : Nat := 1366380579625032171287209

theorem tailTrace_7983050 : CollatzResearch.WordTrace tailWord_7983050 prefixEnd_7983050 1366380579625032171287209 := by
  unfold tailWord_7983050
  simp only [CollatzResearch.WordTrace]
  refine ⟨72791438432195180309894651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194110502485853814159719069 72791438432195180309894651)
  ·
    refine ⟨109187157648292770464841977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72791438432195180309894651 109187157648292770464841977)
    ·
      refine ⟨81890368236219577848631483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109187157648292770464841977 81890368236219577848631483)
      ·
        refine ⟨122835552354329366772947225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81890368236219577848631483 122835552354329366772947225)
        ·
          refine ⟨92126664265747025079710419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122835552354329366772947225 92126664265747025079710419)
          ·
            refine ⟨138189996398620537619565629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92126664265747025079710419 138189996398620537619565629)
            ·
              refine ⟨51821248649482701607337111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138189996398620537619565629 51821248649482701607337111)
              ·
                refine ⟨77731872974224052411005667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51821248649482701607337111 77731872974224052411005667)
                ·
                  refine ⟨116597809461336078616508501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77731872974224052411005667 116597809461336078616508501)
                  ·
                    refine ⟨1366380579625032171287209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116597809461336078616508501 1366380579625032171287209)
                    ·
                      rfl

theorem cell23_7983050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_7983050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983050 prefixEnd_7983050 := by exact prefixLift 7983050
  have htrace : WordTrace (prefixWord ++ tailWord_7983050) baseStart_7983050 baseEnd_7983050 := by
    simpa [prefixWord, tailWord_7983050, baseEnd_7983050] using wordTrace_append hprefix tailTrace_7983050
  have hstable : (prefixWord ++ tailWord_7983050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983050).length < 2 ^ (prefixWord ++ tailWord_7983050).sum := by decide
  have hdescent : baseEnd_7983050 < baseStart_7983050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983080 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 11]
def baseStart_7983080 : Nat := 118140960795 + 7983080 * 2 ^ 59
def prefixEnd_7983080 : Nat := 4983230072969 + 3 ^ 40 * 7983080 * 2
def baseEnd_7983080 : Nat := 455461904810525710720721

theorem tailTrace_7983080 : CollatzResearch.WordTrace tailWord_7983080 prefixEnd_7983080 455461904810525710720721 := by
  unfold tailWord_7983080
  simp only [CollatzResearch.WordTrace]
  refine ⟨145583423959336018181585347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194111231945781357575447129 145583423959336018181585347)
  ·
    refine ⟨218375135939004027272378021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145583423959336018181585347 218375135939004027272378021)
    ·
      refine ⟨40945337988563255113570879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218375135939004027272378021 40945337988563255113570879)
      ·
        refine ⟨61418006982844882670356319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40945337988563255113570879 61418006982844882670356319)
        ·
          refine ⟨92127010474267324005534479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61418006982844882670356319 92127010474267324005534479)
          ·
            refine ⟨138190515711400986008301719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92127010474267324005534479 138190515711400986008301719)
            ·
              refine ⟨207285773567101479012452579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138190515711400986008301719 207285773567101479012452579)
              ·
                refine ⟨310928660350652218518678869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207285773567101479012452579 310928660350652218518678869)
                ·
                  refine ⟨455461904810525710720721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 310928660350652218518678869 455461904810525710720721)
                  ·
                    rfl

theorem cell23_7983080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 11].length) (baseStart_7983080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983080 prefixEnd_7983080 := by exact prefixLift 7983080
  have htrace : WordTrace (prefixWord ++ tailWord_7983080) baseStart_7983080 baseEnd_7983080 := by
    simpa [prefixWord, tailWord_7983080, baseEnd_7983080] using wordTrace_append hprefix tailTrace_7983080
  have hstable : (prefixWord ++ tailWord_7983080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983080).length < 2 ^ (prefixWord ++ tailWord_7983080).sum := by decide
  have hdescent : baseEnd_7983080 < baseStart_7983080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983085 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7983085 : Nat := 118140960795 + 7983085 * 2 ^ 59
def prefixEnd_7983085 : Nat := 4983230072969 + 3 ^ 40 * 7983085 * 2
def baseEnd_7983085 : Nat := 4099159710698003876923967

theorem tailTrace_7983085 : CollatzResearch.WordTrace tailWord_7983085 prefixEnd_7983085 4099159710698003876923967 := by
  unfold tailWord_7983085
  simp only [CollatzResearch.WordTrace]
  refine ⟨291167030283653922217102709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194111353522435948144735139 291167030283653922217102709)
  ·
    refine ⟨27296909089092555207853379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291167030283653922217102709 27296909089092555207853379)
    ·
      refine ⟨40945363633638832811780069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27296909089092555207853379 40945363633638832811780069)
      ·
        refine ⟨7677255681307281152208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40945363633638832811780069 7677255681307281152208763)
        ·
          refine ⟨11515883521960921728313145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677255681307281152208763 11515883521960921728313145)
          ·
            refine ⟨8636912641470691296234859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11515883521960921728313145 8636912641470691296234859)
            ·
              refine ⟨12955368962206036944352289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636912641470691296234859 12955368962206036944352289)
              ·
                refine ⟨9716526721654527708264217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12955368962206036944352289 9716526721654527708264217)
                ·
                  refine ⟨7287395041240895781198163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9716526721654527708264217 7287395041240895781198163)
                  ·
                    refine ⟨10931092561861343671797245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287395041240895781198163 10931092561861343671797245)
                    ·
                      refine ⟨4099159710698003876923967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931092561861343671797245 4099159710698003876923967)
                      ·
                        rfl

theorem cell23_7983085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7983085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983085 prefixEnd_7983085 := by exact prefixLift 7983085
  have htrace : WordTrace (prefixWord ++ tailWord_7983085) baseStart_7983085 baseEnd_7983085 := by
    simpa [prefixWord, tailWord_7983085, baseEnd_7983085] using wordTrace_append hprefix tailTrace_7983085
  have hstable : (prefixWord ++ tailWord_7983085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983085).length < 2 ^ (prefixWord ++ tailWord_7983085).sum := by decide
  have hdescent : baseEnd_7983085 < baseStart_7983085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983097 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 7]
def baseStart_7983097 : Nat := 118140960795 + 7983097 * 2 ^ 59
def prefixEnd_7983097 : Nat := 4983230072969 + 3 ^ 40 * 7983097 * 2
def baseEnd_7983097 : Nat := 455462874718428647774879

theorem tailTrace_7983097 : CollatzResearch.WordTrace tailWord_7983097 prefixEnd_7983097 455462874718428647774879 := by
  unfold tailWord_7983097
  simp only [CollatzResearch.WordTrace]
  refine ⟨291167467959610448266539545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194111645306406965511026363 291167467959610448266539545)
  ·
    refine ⟨218375600969707836199904659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291167467959610448266539545 218375600969707836199904659)
    ·
      refine ⟨327563401454561754299856989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218375600969707836199904659 327563401454561754299856989)
      ·
        refine ⟨122836275545460657862446371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327563401454561754299856989 122836275545460657862446371)
        ·
          refine ⟨184254413318190986793669557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122836275545460657862446371 184254413318190986793669557)
          ·
            refine ⟨17273851248580405011906521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184254413318190986793669557 17273851248580405011906521)
            ·
              refine ⟨12955388436435303758929891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17273851248580405011906521 12955388436435303758929891)
              ·
                refine ⟨19433082654652955638394837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12955388436435303758929891 19433082654652955638394837)
                ·
                  refine ⟨455462874718428647774879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19433082654652955638394837 455462874718428647774879)
                  ·
                    rfl

theorem cell23_7983097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_7983097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983097 prefixEnd_7983097 := by exact prefixLift 7983097
  have htrace : WordTrace (prefixWord ++ tailWord_7983097) baseStart_7983097 baseEnd_7983097 := by
    simpa [prefixWord, tailWord_7983097, baseEnd_7983097] using wordTrace_append hprefix tailTrace_7983097
  have hstable : (prefixWord ++ tailWord_7983097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983097).length < 2 ^ (prefixWord ++ tailWord_7983097).sum := by decide
  have hdescent : baseEnd_7983097 < baseStart_7983097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983120 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_7983120 : Nat := 118140960795 + 7983120 * 2 ^ 59
def prefixEnd_7983120 : Nat := 4983230072969 + 3 ^ 40 * 7983120 * 2
def baseEnd_7983120 : Nat := 4099177682520911239986305

theorem tailTrace_7983120 : CollatzResearch.WordTrace tailWord_7983120 prefixEnd_7983120 4099177682520911239986305 := by
  unfold tailWord_7983120
  simp only [CollatzResearch.WordTrace]
  refine ⟨145584153419263561597313407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194112204559018082129751209 145584153419263561597313407)
  ·
    refine ⟨218376230128895342395970111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145584153419263561597313407 218376230128895342395970111)
    ·
      refine ⟨327564345193343013593955167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218376230128895342395970111 327564345193343013593955167)
      ·
        refine ⟨491346517790014520390932751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327564345193343013593955167 491346517790014520390932751)
        ·
          refine ⟨737019776685021780586399127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491346517790014520390932751 737019776685021780586399127)
          ·
            refine ⟨1105529665027532670879598691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737019776685021780586399127 1105529665027532670879598691)
            ·
              refine ⟨1658294497541299006319398037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105529665027532670879598691 1658294497541299006319398037)
              ·
                refine ⟨77732554572248390921221783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1658294497541299006319398037 77732554572248390921221783)
                ·
                  refine ⟨116598831858372586381832675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77732554572248390921221783 116598831858372586381832675)
                  ·
                    refine ⟨174898247787558879572749013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116598831858372586381832675 174898247787558879572749013)
                    ·
                      refine ⟨4099177682520911239986305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174898247787558879572749013 4099177682520911239986305)
                      ·
                        rfl

theorem cell23_7983120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_7983120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983120 prefixEnd_7983120 := by exact prefixLift 7983120
  have htrace : WordTrace (prefixWord ++ tailWord_7983120) baseStart_7983120 baseEnd_7983120 := by
    simpa [prefixWord, tailWord_7983120, baseEnd_7983120] using wordTrace_append hprefix tailTrace_7983120
  have hstable : (prefixWord ++ tailWord_7983120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983120).length < 2 ^ (prefixWord ++ tailWord_7983120).sum := by decide
  have hdescent : baseEnd_7983120 < baseStart_7983120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983164 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_7983164 : Nat := 118140960795 + 7983164 * 2 ^ 59
def prefixEnd_7983164 : Nat := 4983230072969 + 3 ^ 40 * 7983164 * 2
def baseEnd_7983164 : Nat := 4099200275669709067836103

theorem tailTrace_7983164 : CollatzResearch.WordTrace tailWord_7983164 prefixEnd_7983164 4099200275669709067836103 := by
  unfold tailWord_7983164
  simp only [CollatzResearch.WordTrace]
  refine ⟨145584955825183859354614273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194113274433578479139485697 145584955825183859354614273)
  ·
    refine ⟨109188716868887894515960705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145584955825183859354614273 109188716868887894515960705)
    ·
      refine ⟨81891537651665920886970529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109188716868887894515960705 81891537651665920886970529)
      ·
        refine ⟨61418653238749440665227897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81891537651665920886970529 61418653238749440665227897)
        ·
          refine ⟨46063989929062080498920923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61418653238749440665227897 46063989929062080498920923)
          ·
            refine ⟨69095984893593120748381385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46063989929062080498920923 69095984893593120748381385)
            ·
              refine ⟨51821988670194840561286039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69095984893593120748381385 51821988670194840561286039)
              ·
                refine ⟨77732983005292260841929059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51821988670194840561286039 77732983005292260841929059)
                ·
                  refine ⟨116599474507938391262893589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77732983005292260841929059 116599474507938391262893589)
                  ·
                    refine ⟨5465600367559612090448137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116599474507938391262893589 5465600367559612090448137)
                    ·
                      refine ⟨4099200275669709067836103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465600367559612090448137 4099200275669709067836103)
                      ·
                        rfl

theorem cell23_7983164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_7983164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983164 prefixEnd_7983164 := by exact prefixLift 7983164
  have htrace : WordTrace (prefixWord ++ tailWord_7983164) baseStart_7983164 baseEnd_7983164 := by
    simpa [prefixWord, tailWord_7983164, baseEnd_7983164] using wordTrace_append hprefix tailTrace_7983164
  have hstable : (prefixWord ++ tailWord_7983164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983164).length < 2 ^ (prefixWord ++ tailWord_7983164).sum := by decide
  have hdescent : baseEnd_7983164 < baseStart_7983164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983167 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_7983167 : Nat := 118140960795 + 7983167 * 2 ^ 59
def prefixEnd_7983167 : Nat := 4983230072969 + 3 ^ 40 * 7983167 * 2
def baseEnd_7983167 : Nat := 4099201816111672556098589

theorem tailTrace_7983167 : CollatzResearch.WordTrace tailWord_7983167 prefixEnd_7983167 4099201816111672556098589 := by
  unfold tailWord_7983167
  simp only [CollatzResearch.WordTrace]
  refine ⟨291170021069356850221587755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194113347379571233481058503 291170021069356850221587755)
  ·
    refine ⟨436755031604035275332381633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291170021069356850221587755 436755031604035275332381633)
    ·
      refine ⟨327566273703026456499286225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436755031604035275332381633 327566273703026456499286225)
      ·
        refine ⟨245674705277269842374464669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327566273703026456499286225 245674705277269842374464669)
        ·
          refine ⟨92128014478976190890424251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245674705277269842374464669 92128014478976190890424251)
          ·
            refine ⟨138192021718464286335636377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92128014478976190890424251 138192021718464286335636377)
            ·
              refine ⟨103644016288848214751727283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138192021718464286335636377 103644016288848214751727283)
              ·
                refine ⟨155466024433272322127590925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103644016288848214751727283 155466024433272322127590925)
                ·
                  refine ⟨58299759162477120797846597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155466024433272322127590925 58299759162477120797846597)
                  ·
                    refine ⟨10931204842964460149596237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58299759162477120797846597 10931204842964460149596237)
                    ·
                      refine ⟨4099201816111672556098589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931204842964460149596237 4099201816111672556098589)
                      ·
                        rfl

theorem cell23_7983167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_7983167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983167 prefixEnd_7983167 := by exact prefixLift 7983167
  have htrace : WordTrace (prefixWord ++ tailWord_7983167) baseStart_7983167 baseEnd_7983167 := by
    simpa [prefixWord, tailWord_7983167, baseEnd_7983167] using wordTrace_append hprefix tailTrace_7983167
  have hstable : (prefixWord ++ tailWord_7983167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983167).length < 2 ^ (prefixWord ++ tailWord_7983167).sum := by decide
  have hdescent : baseEnd_7983167 < baseStart_7983167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983181 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_7983181 : Nat := 118140960795 + 7983181 * 2 ^ 59
def prefixEnd_7983181 : Nat := 4983230072969 + 3 ^ 40 * 7983181 * 2
def baseEnd_7983181 : Nat := 4099209004840835501323525

theorem tailTrace_7983181 : CollatzResearch.WordTrace tailWord_7983181 prefixEnd_7983181 4099209004840835501323525 := by
  unfold tailWord_7983181
  simp only [CollatzResearch.WordTrace]
  refine ⟨291170531691306130612597397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194113687794204087075064931 291170531691306130612597397)
  ·
    refine ⟨13648618673029974872465503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291170531691306130612597397 13648618673029974872465503)
    ·
      refine ⟨20472928009544962308698255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13648618673029974872465503 20472928009544962308698255)
      ·
        refine ⟨30709392014317443463047383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20472928009544962308698255 30709392014317443463047383)
        ·
          refine ⟨46064088021476165194571075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30709392014317443463047383 46064088021476165194571075)
          ·
            refine ⟨69096132032214247791856613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46064088021476165194571075 69096132032214247791856613)
            ·
              refine ⟨12955524756040171460973115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69096132032214247791856613 12955524756040171460973115)
              ·
                refine ⟨19433287134060257191459673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12955524756040171460973115 19433287134060257191459673)
                ·
                  refine ⟨14574965350545192893594755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19433287134060257191459673 14574965350545192893594755)
                  ·
                    refine ⟨21862448025817789340392133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14574965350545192893594755 21862448025817789340392133)
                    ·
                      refine ⟨4099209004840835501323525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21862448025817789340392133 4099209004840835501323525)
                      ·
                        rfl

theorem cell23_7983181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_7983181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983181 prefixEnd_7983181 := by exact prefixLift 7983181
  have htrace : WordTrace (prefixWord ++ tailWord_7983181) baseStart_7983181 baseEnd_7983181 := by
    simpa [prefixWord, tailWord_7983181, baseEnd_7983181] using wordTrace_append hprefix tailTrace_7983181
  have hstable : (prefixWord ++ tailWord_7983181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983181).length < 2 ^ (prefixWord ++ tailWord_7983181).sum := by decide
  have hdescent : baseEnd_7983181 < baseStart_7983181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983207 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_7983207 : Nat := 118140960795 + 7983207 * 2 ^ 59
def prefixEnd_7983207 : Nat := 4983230072969 + 3 ^ 40 * 7983207 * 2
def baseEnd_7983207 : Nat := 4099222355337852399598405

theorem tailTrace_7983207 : CollatzResearch.WordTrace tailWord_7983207 prefixEnd_7983207 4099222355337852399598405 := by
  unfold tailWord_7983207
  simp only [CollatzResearch.WordTrace]
  refine ⟨291171479989211937053043875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194114319992807958035362583 291171479989211937053043875)
  ·
    refine ⟨436757219983817905579565813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291171479989211937053043875 436757219983817905579565813)
    ·
      refine ⟨40945989373482928648084295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436757219983817905579565813 40945989373482928648084295)
      ·
        refine ⟨61418984060224392972126443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40945989373482928648084295 61418984060224392972126443)
        ·
          refine ⟨92128476090336589458189665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61418984060224392972126443 92128476090336589458189665)
          ·
            refine ⟨69096357067752442093642249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92128476090336589458189665 69096357067752442093642249)
            ·
              refine ⟨51822267800814331570231687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69096357067752442093642249 51822267800814331570231687)
              ·
                refine ⟨77733401701221497355347531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51822267800814331570231687 77733401701221497355347531)
                ·
                  refine ⟨116600102551832246033021297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77733401701221497355347531 116600102551832246033021297)
                  ·
                    refine ⟨87450076913874184524765973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116600102551832246033021297 87450076913874184524765973)
                    ·
                      refine ⟨4099222355337852399598405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87450076913874184524765973 4099222355337852399598405)
                      ·
                        rfl

theorem cell23_7983207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_7983207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983207 prefixEnd_7983207 := by exact prefixLift 7983207
  have htrace : WordTrace (prefixWord ++ tailWord_7983207) baseStart_7983207 baseEnd_7983207 := by
    simpa [prefixWord, tailWord_7983207, baseEnd_7983207] using wordTrace_append hprefix tailTrace_7983207
  have hstable : (prefixWord ++ tailWord_7983207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983207).length < 2 ^ (prefixWord ++ tailWord_7983207).sum := by decide
  have hdescent : baseEnd_7983207 < baseStart_7983207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983217 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_7983217 : Nat := 118140960795 + 7983217 * 2 ^ 59
def prefixEnd_7983217 : Nat := 4983230072969 + 3 ^ 40 * 7983217 * 2
def baseEnd_7983217 : Nat := 1366409163381465786824453

theorem tailTrace_7983217 : CollatzResearch.WordTrace tailWord_7983217 prefixEnd_7983217 1366409163381465786824453 := by
  unfold tailWord_7983217
  simp only [CollatzResearch.WordTrace]
  refine ⟨291171844719175708760907905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194114563146117139173938603 291171844719175708760907905)
  ·
    refine ⟨218378883539381781570680929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291171844719175708760907905 218378883539381781570680929)
    ·
      refine ⟨163784162654536336178010697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218378883539381781570680929 163784162654536336178010697)
      ·
        refine ⟨122838121990902252133508023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163784162654536336178010697 122838121990902252133508023)
        ·
          refine ⟨184257182986353378200262035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122838121990902252133508023 184257182986353378200262035)
          ·
            refine ⟨276385774479530067300393053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184257182986353378200262035 276385774479530067300393053)
            ·
              refine ⟨103644665429823775237647395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276385774479530067300393053 103644665429823775237647395)
              ·
                refine ⟨155466998144735662856471093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103644665429823775237647395 155466998144735662856471093)
                ·
                  refine ⟨14575031076068968392794165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155466998144735662856471093 14575031076068968392794165)
                  ·
                    refine ⟨1366409163381465786824453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14575031076068968392794165 1366409163381465786824453)
                    ·
                      rfl

theorem cell23_7983217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_7983217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983217 prefixEnd_7983217 := by exact prefixLift 7983217
  have htrace : WordTrace (prefixWord ++ tailWord_7983217) baseStart_7983217 baseEnd_7983217 := by
    simpa [prefixWord, tailWord_7983217, baseEnd_7983217] using wordTrace_append hprefix tailTrace_7983217
  have hstable : (prefixWord ++ tailWord_7983217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983217).length < 2 ^ (prefixWord ++ tailWord_7983217).sum := by decide
  have hdescent : baseEnd_7983217 < baseStart_7983217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983224 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_7983224 : Nat := 118140960795 + 7983224 * 2 ^ 59
def prefixEnd_7983224 : Nat := 4983230072969 + 3 ^ 40 * 7983224 * 2
def baseEnd_7983224 : Nat := 4099231084508978833085827

theorem tailTrace_7983224 : CollatzResearch.WordTrace tailWord_7983224 prefixEnd_7983224 4099231084508978833085827 := by
  unfold tailWord_7983224
  simp only [CollatzResearch.WordTrace]
  refine ⟨145586050015075174478206363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194114733353433565970941817 145586050015075174478206363)
  ·
    refine ⟨218379075022612761717309545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145586050015075174478206363 218379075022612761717309545)
    ·
      refine ⟨163784306266959571287982159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218379075022612761717309545 163784306266959571287982159)
      ·
        refine ⟨245676459400439356931973239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163784306266959571287982159 245676459400439356931973239)
        ·
          refine ⟨368514689100659035397959859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245676459400439356931973239 368514689100659035397959859)
          ·
            refine ⟨552772033650988553096939789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368514689100659035397959859 552772033650988553096939789)
            ·
              refine ⟨207289512619120707411352421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552772033650988553096939789 207289512619120707411352421)
              ·
                refine ⟨38866783616085132639628579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207289512619120707411352421 38866783616085132639628579)
                ·
                  refine ⟨58300175424127698959442869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38866783616085132639628579 58300175424127698959442869)
                  ·
                    refine ⟨5465641446011971777447769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58300175424127698959442869 5465641446011971777447769)
                    ·
                      refine ⟨4099231084508978833085827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465641446011971777447769 4099231084508978833085827)
                      ·
                        rfl

theorem cell23_7983224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_7983224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983224 prefixEnd_7983224 := by exact prefixLift 7983224
  have htrace : WordTrace (prefixWord ++ tailWord_7983224) baseStart_7983224 baseEnd_7983224 := by
    simpa [prefixWord, tailWord_7983224, baseEnd_7983224] using wordTrace_append hprefix tailTrace_7983224
  have hstable : (prefixWord ++ tailWord_7983224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983224).length < 2 ^ (prefixWord ++ tailWord_7983224).sum := by decide
  have hdescent : baseEnd_7983224 < baseStart_7983224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983248 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 1, 1, 3]
def baseStart_7983248 : Nat := 118140960795 + 7983248 * 2 ^ 59
def prefixEnd_7983248 : Nat := 4983230072969 + 3 ^ 40 * 7983248 * 2
def baseEnd_7983248 : Nat := 4099243408044686739185717

theorem tailTrace_7983248 : CollatzResearch.WordTrace tailWord_7983248 prefixEnd_7983248 4099243408044686739185717 := by
  unfold tailWord_7983248
  simp only [CollatzResearch.WordTrace]
  refine ⟨145586487691031700527643199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194115316921375600703524265 145586487691031700527643199)
  ·
    refine ⟨218379731536547550791464799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145586487691031700527643199 218379731536547550791464799)
    ·
      refine ⟨327569597304821326187197199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218379731536547550791464799 327569597304821326187197199)
      ·
        refine ⟨491354395957231989280795799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327569597304821326187197199 491354395957231989280795799)
        ·
          refine ⟨737031593935847983921193699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491354395957231989280795799 737031593935847983921193699)
          ·
            refine ⟨1105547390903771975881790549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737031593935847983921193699 1105547390903771975881790549)
            ·
              refine ⟨12955633487153577842364733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1105547390903771975881790549 12955633487153577842364733)
              ·
                refine ⟨4858362557682591690886775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12955633487153577842364733 4858362557682591690886775)
                ·
                  refine ⟨7287543836523887536330163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858362557682591690886775 7287543836523887536330163)
                  ·
                    refine ⟨10931315754785831304495245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287543836523887536330163 10931315754785831304495245)
                    ·
                      refine ⟨4099243408044686739185717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931315754785831304495245 4099243408044686739185717)
                      ·
                        rfl

theorem cell23_7983248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 1, 3].length) (baseStart_7983248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983248 prefixEnd_7983248 := by exact prefixLift 7983248
  have htrace : WordTrace (prefixWord ++ tailWord_7983248) baseStart_7983248 baseEnd_7983248 := by
    simpa [prefixWord, tailWord_7983248, baseEnd_7983248] using wordTrace_append hprefix tailTrace_7983248
  have hstable : (prefixWord ++ tailWord_7983248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983248).length < 2 ^ (prefixWord ++ tailWord_7983248).sum := by decide
  have hdescent : baseEnd_7983248 < baseStart_7983248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_7983257 : Nat := 118140960795 + 7983257 * 2 ^ 59
def prefixEnd_7983257 : Nat := 4983230072969 + 3 ^ 40 * 7983257 * 2
def baseEnd_7983257 : Nat := 4099248029370577203973175

theorem tailTrace_7983257 : CollatzResearch.WordTrace tailWord_7983257 prefixEnd_7983257 4099248029370577203973175 := by
  unfold tailWord_7983257
  simp only [CollatzResearch.WordTrace]
  refine ⟨291173303639030795592364025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194115535759353863728242683 291173303639030795592364025)
  ·
    refine ⟨218379977729273096694273019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291173303639030795592364025 218379977729273096694273019)
    ·
      refine ⟨327569966593909645041409529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218379977729273096694273019 327569966593909645041409529)
      ·
        refine ⟨245677474945432233781057147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327569966593909645041409529 245677474945432233781057147)
        ·
          refine ⟨368516212418148350671585721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245677474945432233781057147 368516212418148350671585721)
          ·
            refine ⟨276387159313611263003689291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368516212418148350671585721 276387159313611263003689291)
            ·
              refine ⟨414580738970416894505533937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276387159313611263003689291 414580738970416894505533937)
              ·
                refine ⟨310935554227812670879150453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414580738970416894505533937 310935554227812670879150453)
                ·
                  refine ⟨29150208208857437894920355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310935554227812670879150453 29150208208857437894920355)
                  ·
                    refine ⟨43725312313286156842380533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29150208208857437894920355 43725312313286156842380533)
                    ·
                      refine ⟨4099248029370577203973175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43725312313286156842380533 4099248029370577203973175)
                      ·
                        rfl

theorem cell23_7983257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_7983257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983257 prefixEnd_7983257 := by exact prefixLift 7983257
  have htrace : WordTrace (prefixWord ++ tailWord_7983257) baseStart_7983257 baseEnd_7983257 := by
    simpa [prefixWord, tailWord_7983257, baseEnd_7983257] using wordTrace_append hprefix tailTrace_7983257
  have hstable : (prefixWord ++ tailWord_7983257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983257).length < 2 ^ (prefixWord ++ tailWord_7983257).sum := by decide
  have hdescent : baseEnd_7983257 < baseStart_7983257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983267 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7983267 : Nat := 118140960795 + 7983267 * 2 ^ 59
def prefixEnd_7983267 : Nat := 4983230072969 + 3 ^ 40 * 7983267 * 2
def baseEnd_7983267 : Nat := 4099253164177122164848129

theorem tailTrace_7983267 : CollatzResearch.WordTrace tailWord_7983267 prefixEnd_7983267 4099253164177122164848129 := by
  unfold tailWord_7983267
  simp only [CollatzResearch.WordTrace]
  refine ⟨291173668368994567300228055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194115778912663044866818703 291173668368994567300228055)
  ·
    refine ⟨436760502553491850950342083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291173668368994567300228055 436760502553491850950342083)
    ·
      refine ⟨655140753830237776425513125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436760502553491850950342083 655140753830237776425513125)
      ·
        refine ⟨122838891343169583079783711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655140753830237776425513125 122838891343169583079783711)
        ·
          refine ⟨184258337014754374619675567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122838891343169583079783711 184258337014754374619675567)
          ·
            refine ⟨276387505522131561929513351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184258337014754374619675567 276387505522131561929513351)
            ·
              refine ⟨414581258283197342894270027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276387505522131561929513351 414581258283197342894270027)
              ·
                refine ⟨621871887424796014341405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414581258283197342894270027 621871887424796014341405041)
                ·
                  refine ⟨466403915568597010756053781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621871887424796014341405041 466403915568597010756053781)
                  ·
                    refine ⟨21862683542277984879190021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 466403915568597010756053781 21862683542277984879190021)
                    ·
                      refine ⟨4099253164177122164848129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21862683542277984879190021 4099253164177122164848129)
                      ·
                        rfl

theorem cell23_7983267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7983267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983267 prefixEnd_7983267 := by exact prefixLift 7983267
  have htrace : WordTrace (prefixWord ++ tailWord_7983267) baseStart_7983267 baseEnd_7983267 := by
    simpa [prefixWord, tailWord_7983267, baseEnd_7983267] using wordTrace_append hprefix tailTrace_7983267
  have hstable : (prefixWord ++ tailWord_7983267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983267).length < 2 ^ (prefixWord ++ tailWord_7983267).sum := by decide
  have hdescent : baseEnd_7983267 < baseStart_7983267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983291 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 3]
def baseStart_7983291 : Nat := 118140960795 + 7983291 * 2 ^ 59
def prefixEnd_7983291 : Nat := 4983230072969 + 3 ^ 40 * 7983291 * 2
def baseEnd_7983291 : Nat := 4099265487712830070948019

theorem tailTrace_7983291 : CollatzResearch.WordTrace tailWord_7983291 prefixEnd_7983291 4099265487712830070948019 := by
  unfold tailWord_7983291
  simp only [CollatzResearch.WordTrace]
  refine ⟨291174543720907619399101727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194116362480605079599401151 291174543720907619399101727)
  ·
    refine ⟨436761815581361429098652591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291174543720907619399101727 436761815581361429098652591)
    ·
      refine ⟨655142723372042143647978887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436761815581361429098652591 655142723372042143647978887)
      ·
        refine ⟨982714085058063215471968331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655142723372042143647978887 982714085058063215471968331)
        ·
          refine ⟨1474071127587094823207952497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982714085058063215471968331 1474071127587094823207952497)
          ·
            refine ⟨1105553345690321117405964373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474071127587094823207952497 1105553345690321117405964373)
            ·
              refine ⟨12955703269808450594601145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1105553345690321117405964373 12955703269808450594601145)
              ·
                refine ⟨9716777452356337945950859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12955703269808450594601145 9716777452356337945950859)
                ·
                  refine ⟨14575166178534506918926289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9716777452356337945950859 14575166178534506918926289)
                  ·
                    refine ⟨10931374633900880189194717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14575166178534506918926289 10931374633900880189194717)
                    ·
                      refine ⟨4099265487712830070948019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931374633900880189194717 4099265487712830070948019)
                      ·
                        rfl

theorem cell23_7983291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 3].length) (baseStart_7983291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983291 prefixEnd_7983291 := by exact prefixLift 7983291
  have htrace : WordTrace (prefixWord ++ tailWord_7983291) baseStart_7983291 baseEnd_7983291 := by
    simpa [prefixWord, tailWord_7983291, baseEnd_7983291] using wordTrace_append hprefix tailTrace_7983291
  have hstable : (prefixWord ++ tailWord_7983291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983291).length < 2 ^ (prefixWord ++ tailWord_7983291).sum := by decide
  have hdescent : baseEnd_7983291 < baseStart_7983291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983304 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_7983304 : Nat := 118140960795 + 7983304 * 2 ^ 59
def prefixEnd_7983304 : Nat := 4983230072969 + 3 ^ 40 * 7983304 * 2
def baseEnd_7983304 : Nat := 4099272162961338520085459

theorem tailTrace_7983304 : CollatzResearch.WordTrace tailWord_7983304 prefixEnd_7983304 4099272162961338520085459 := by
  unfold tailWord_7983304
  simp only [CollatzResearch.WordTrace]
  refine ⟨145587508934930261309662483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194116678579907015079549977 145587508934930261309662483)
  ·
    refine ⟨218381263402395391964493725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145587508934930261309662483 218381263402395391964493725)
    ·
      refine ⟨81892973775898271986685147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218381263402395391964493725 81892973775898271986685147)
      ·
        refine ⟨122839460663847407980027721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81892973775898271986685147 122839460663847407980027721)
        ·
          refine ⟨92129595497885555985020791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122839460663847407980027721 92129595497885555985020791)
          ·
            refine ⟨138194393246828333977531187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92129595497885555985020791 138194393246828333977531187)
            ·
              refine ⟨207291589870242500966296781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138194393246828333977531187 207291589870242500966296781)
              ·
                refine ⟨77734346201340937862361293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207291589870242500966296781 77734346201340937862361293)
                ·
                  refine ⟨29150379825502851698385485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77734346201340937862361293 29150379825502851698385485)
                  ·
                    refine ⟨10931392434563569386894557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29150379825502851698385485 10931392434563569386894557)
                    ·
                      refine ⟨4099272162961338520085459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931392434563569386894557 4099272162961338520085459)
                      ·
                        rfl

theorem cell23_7983304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_7983304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983304 prefixEnd_7983304 := by exact prefixLift 7983304
  have htrace : WordTrace (prefixWord ++ tailWord_7983304) baseStart_7983304 baseEnd_7983304 := by
    simpa [prefixWord, tailWord_7983304, baseEnd_7983304] using wordTrace_append hprefix tailTrace_7983304
  have hstable : (prefixWord ++ tailWord_7983304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983304).length < 2 ^ (prefixWord ++ tailWord_7983304).sum := by decide
  have hdescent : baseEnd_7983304 < baseStart_7983304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983308 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7983308 : Nat := 118140960795 + 7983308 * 2 ^ 59
def prefixEnd_7983308 : Nat := 4983230072969 + 3 ^ 40 * 7983308 * 2
def baseEnd_7983308 : Nat := 4099274216883956504435441

theorem tailTrace_7983308 : CollatzResearch.WordTrace tailWord_7983308 prefixEnd_7983308 4099274216883956504435441 := by
  unfold tailWord_7983308
  simp only [CollatzResearch.WordTrace]
  refine ⟨145587581880923015651235289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194116775841230687534980385 145587581880923015651235289)
  ·
    refine ⟨109190686410692261738426467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145587581880923015651235289 109190686410692261738426467)
    ·
      refine ⟨163786029616038392607639701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109190686410692261738426467 163786029616038392607639701)
      ·
        refine ⟨7677470138251799653483111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163786029616038392607639701 7677470138251799653483111)
        ·
          refine ⟨11516205207377699480224667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677470138251799653483111 11516205207377699480224667)
          ·
            refine ⟨17274307811066549220337001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11516205207377699480224667 17274307811066549220337001)
            ·
              refine ⟨12955730858299911915252751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17274307811066549220337001 12955730858299911915252751)
              ·
                refine ⟨19433596287449867872879127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12955730858299911915252751 19433596287449867872879127)
                ·
                  refine ⟨29150394431174801809318691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19433596287449867872879127 29150394431174801809318691)
                  ·
                    refine ⟨43725591646762202713978037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29150394431174801809318691 43725591646762202713978037)
                    ·
                      refine ⟨4099274216883956504435441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43725591646762202713978037 4099274216883956504435441)
                      ·
                        rfl

theorem cell23_7983308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7983308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983308 prefixEnd_7983308 := by exact prefixLift 7983308
  have htrace : WordTrace (prefixWord ++ tailWord_7983308) baseStart_7983308 baseEnd_7983308 := by
    simpa [prefixWord, tailWord_7983308, baseEnd_7983308] using wordTrace_append hprefix tailTrace_7983308
  have hstable : (prefixWord ++ tailWord_7983308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983308).length < 2 ^ (prefixWord ++ tailWord_7983308).sum := by decide
  have hdescent : baseEnd_7983308 < baseStart_7983308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983321 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_7983321 : Nat := 118140960795 + 7983321 * 2 ^ 59
def prefixEnd_7983321 : Nat := 4983230072969 + 3 ^ 40 * 7983321 * 2
def baseEnd_7983321 : Nat := 4099280892132464953572881

theorem tailTrace_7983321 : CollatzResearch.WordTrace tailWord_7983321 prefixEnd_7983321 4099280892132464953572881 := by
  unfold tailWord_7983321
  simp only [CollatzResearch.WordTrace]
  refine ⟨291175637910798934522693817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194117091940532623015129211 291175637910798934522693817)
  ·
    refine ⟨218381728433099200892020363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291175637910798934522693817 218381728433099200892020363)
    ·
      refine ⟨327572592649648801338030545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218381728433099200892020363 327572592649648801338030545)
      ·
        refine ⟨245679444487236601003522909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327572592649648801338030545 245679444487236601003522909)
        ·
          refine ⟨92129791682713725376321091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245679444487236601003522909 92129791682713725376321091)
          ·
            refine ⟨138194687524070588064481637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92129791682713725376321091 138194687524070588064481637)
            ·
              refine ⟨25911503910763235262090307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138194687524070588064481637 25911503910763235262090307)
              ·
                refine ⟨38867255866144852893135461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25911503910763235262090307 38867255866144852893135461)
                ·
                  refine ⟨7287610474902159917462899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38867255866144852893135461 7287610474902159917462899)
                  ·
                    refine ⟨10931415712353239876194349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287610474902159917462899 10931415712353239876194349)
                    ·
                      refine ⟨4099280892132464953572881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931415712353239876194349 4099280892132464953572881)
                      ·
                        rfl

theorem cell23_7983321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_7983321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983321 prefixEnd_7983321 := by exact prefixLift 7983321
  have htrace : WordTrace (prefixWord ++ tailWord_7983321) baseStart_7983321 baseEnd_7983321 := by
    simpa [prefixWord, tailWord_7983321, baseEnd_7983321] using wordTrace_append hprefix tailTrace_7983321
  have hstable : (prefixWord ++ tailWord_7983321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983321).length < 2 ^ (prefixWord ++ tailWord_7983321).sum := by decide
  have hdescent : baseEnd_7983321 < baseStart_7983321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983338 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_7983338 : Nat := 118140960795 + 7983338 * 2 ^ 59
def prefixEnd_7983338 : Nat := 4983230072969 + 3 ^ 40 * 7983338 * 2
def baseEnd_7983338 : Nat := 4099289621303591387060303

theorem tailTrace_7983338 : CollatzResearch.WordTrace tailWord_7983338 prefixEnd_7983338 4099289621303591387060303 := by
  unfold tailWord_7983338
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794064487934336606515667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194117505301158230950708445 72794064487934336606515667)
  ·
    refine ⟨109191096731901504909773501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72794064487934336606515667 109191096731901504909773501)
    ·
      refine ⟨40946661274463064341165063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109191096731901504909773501 40946661274463064341165063)
      ·
        refine ⟨61419991911694596511747595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40946661274463064341165063 61419991911694596511747595)
        ·
          refine ⟨92129987867541894767621393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61419991911694596511747595 92129987867541894767621393)
          ·
            refine ⟨69097490900656421075716045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92129987867541894767621393 69097490900656421075716045)
            ·
              refine ⟨25911559087746157903393517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69097490900656421075716045 25911559087746157903393517)
              ·
                refine ⟨9716834657904809213772569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25911559087746157903393517 9716834657904809213772569)
                ·
                  refine ⟨7287625993428606910329427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9716834657904809213772569 7287625993428606910329427)
                  ·
                    refine ⟨10931438990142910365494141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7287625993428606910329427 10931438990142910365494141)
                    ·
                      refine ⟨4099289621303591387060303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931438990142910365494141 4099289621303591387060303)
                      ·
                        rfl

theorem cell23_7983338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_7983338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983338 prefixEnd_7983338 := by exact prefixLift 7983338
  have htrace : WordTrace (prefixWord ++ tailWord_7983338) baseStart_7983338 baseEnd_7983338 := by
    simpa [prefixWord, tailWord_7983338, baseEnd_7983338] using wordTrace_append hprefix tailTrace_7983338
  have hstable : (prefixWord ++ tailWord_7983338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983338).length < 2 ^ (prefixWord ++ tailWord_7983338).sum := by decide
  have hdescent : baseEnd_7983338 < baseStart_7983338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983384 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 7]
def baseStart_7983384 : Nat := 118140960795 + 7983384 * 2 ^ 59
def prefixEnd_7983384 : Nat := 4983230072969 + 3 ^ 40 * 7983384 * 2
def baseEnd_7983384 : Nat := 455479249045966467453899

theorem tailTrace_7983384 : CollatzResearch.WordTrace tailWord_7983384 prefixEnd_7983384 455479249045966467453899 := by
  unfold tailWord_7983384
  simp only [CollatzResearch.WordTrace]
  refine ⟨145588967854785348141118603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194118623806380464188158137 145588967854785348141118603)
  ·
    refine ⟨218383451782178022211677905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145588967854785348141118603 218383451782178022211677905)
    ·
      refine ⟨163787588836633516658758429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218383451782178022211677905 163787588836633516658758429)
      ·
        refine ⟨61420345813737568747034411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163787588836633516658758429 61420345813737568747034411)
        ·
          refine ⟨92130518720606353120551617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61420345813737568747034411 92130518720606353120551617)
          ·
            refine ⟨69097889040454764840413713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92130518720606353120551617 69097889040454764840413713)
            ·
              refine ⟨51823416780341073630310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69097889040454764840413713 51823416780341073630310285)
              ·
                refine ⟨19433781292627902611366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51823416780341073630310285 19433781292627902611366357)
                ·
                  refine ⟨455479249045966467453899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19433781292627902611366357 455479249045966467453899)
                  ·
                    rfl

theorem cell23_7983384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_7983384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983384 prefixEnd_7983384 := by exact prefixLift 7983384
  have htrace : WordTrace (prefixWord ++ tailWord_7983384) baseStart_7983384 baseEnd_7983384 := by
    simpa [prefixWord, tailWord_7983384, baseEnd_7983384] using wordTrace_append hprefix tailTrace_7983384
  have hstable : (prefixWord ++ tailWord_7983384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983384).length < 2 ^ (prefixWord ++ tailWord_7983384).sum := by decide
  have hdescent : baseEnd_7983384 < baseStart_7983384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983391 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7983391 : Nat := 118140960795 + 7983391 * 2 ^ 59
def prefixEnd_7983391 : Nat := 4983230072969 + 3 ^ 40 * 7983391 * 2
def baseEnd_7983391 : Nat := 4099316835778279679697559

theorem tailTrace_7983391 : CollatzResearch.WordTrace tailWord_7983391 prefixEnd_7983391 4099316835778279679697559 := by
  unfold tailWord_7983391
  simp only [CollatzResearch.WordTrace]
  refine ⟨291178191020545336477742027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194118794013696890985161351 291178191020545336477742027)
  ·
    refine ⟨436767286530818004716613041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291178191020545336477742027 436767286530818004716613041)
    ·
      refine ⟨327575464898113503537459781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436767286530818004716613041 327575464898113503537459781)
      ·
        refine ⟨61420399668396281913273709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327575464898113503537459781 61420399668396281913273709)
        ·
          refine ⟨23032649875648605717477641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61420399668396281913273709 23032649875648605717477641)
          ·
            refine ⟨17274487406736454288108231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23032649875648605717477641 17274487406736454288108231)
            ·
              refine ⟨25911731110104681432162347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17274487406736454288108231 25911731110104681432162347)
              ·
                refine ⟨38867596665157022148243521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25911731110104681432162347 38867596665157022148243521)
                ·
                  refine ⟨29150697498867766611182641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38867596665157022148243521 29150697498867766611182641)
                  ·
                    refine ⟨21863023124150824958386981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29150697498867766611182641 21863023124150824958386981)
                    ·
                      refine ⟨4099316835778279679697559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21863023124150824958386981 4099316835778279679697559)
                      ·
                        rfl

theorem cell23_7983391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7983391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983391 prefixEnd_7983391 := by exact prefixLift 7983391
  have htrace : WordTrace (prefixWord ++ tailWord_7983391) baseStart_7983391 baseEnd_7983391 := by
    simpa [prefixWord, tailWord_7983391, baseEnd_7983391] using wordTrace_append hprefix tailTrace_7983391
  have hstable : (prefixWord ++ tailWord_7983391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983391).length < 2 ^ (prefixWord ++ tailWord_7983391).sum := by decide
  have hdescent : baseEnd_7983391 < baseStart_7983391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983418 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_7983418 : Nat := 118140960795 + 7983418 * 2 ^ 59
def prefixEnd_7983418 : Nat := 4983230072969 + 3 ^ 40 * 7983418 * 2
def baseEnd_7983418 : Nat := 455481188861772341562215

theorem tailTrace_7983418 : CollatzResearch.WordTrace tailWord_7983418 prefixEnd_7983418 455481188861772341562215 := by
  unfold tailWord_7983418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794793947861880022243727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194119450527631680059316605 72794793947861880022243727)
  ·
    refine ⟨109192190921792820033365591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72794793947861880022243727 109192190921792820033365591)
    ·
      refine ⟨163788286382689230050048387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109192190921792820033365591 163788286382689230050048387)
      ·
        refine ⟨245682429574033845075072581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163788286382689230050048387 245682429574033845075072581)
        ·
          refine ⟨46065455545131345951576109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245682429574033845075072581 46065455545131345951576109)
          ·
            refine ⟨17274545829424254731841041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46065455545131345951576109 17274545829424254731841041)
            ·
              refine ⟨12955909372068191048880781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17274545829424254731841041 12955909372068191048880781)
              ·
                refine ⟨4858466014525571643330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12955909372068191048880781 4858466014525571643330293)
                ·
                  refine ⟨455481188861772341562215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858466014525571643330293 455481188861772341562215)
                  ·
                    rfl

theorem cell23_7983418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_7983418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983418 prefixEnd_7983418 := by exact prefixLift 7983418
  have htrace : WordTrace (prefixWord ++ tailWord_7983418) baseStart_7983418 baseEnd_7983418 := by
    simpa [prefixWord, tailWord_7983418, baseEnd_7983418] using wordTrace_append hprefix tailTrace_7983418
  have hstable : (prefixWord ++ tailWord_7983418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983418).length < 2 ^ (prefixWord ++ tailWord_7983418).sum := by decide
  have hdescent : baseEnd_7983418 < baseStart_7983418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983424 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_7983424 : Nat := 118140960795 + 7983424 * 2 ^ 59
def prefixEnd_7983424 : Nat := 4983230072969 + 3 ^ 40 * 7983424 * 2
def baseEnd_7983424 : Nat := 4099333780639878050584907

theorem tailTrace_7983424 : CollatzResearch.WordTrace tailWord_7983424 prefixEnd_7983424 4099333780639878050584907 := by
  unfold tailWord_7983424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145589697314712891556846663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194119596419617188742462217 145589697314712891556846663)
  ·
    refine ⟨218384545972069337335269995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145589697314712891556846663 218384545972069337335269995)
    ·
      refine ⟨327576818958104006002904993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218384545972069337335269995 327576818958104006002904993)
      ·
        refine ⟨245682614218578004502178745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327576818958104006002904993 245682614218578004502178745)
        ·
          refine ⟨184261960663933503376634059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245682614218578004502178745 184261960663933503376634059)
          ·
            refine ⟨276392940995900255064951089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184261960663933503376634059 276392940995900255064951089)
            ·
              refine ⟨207294705746925191298713317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276392940995900255064951089 207294705746925191298713317)
              ·
                refine ⟨38867757327548473368508747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207294705746925191298713317 38867757327548473368508747)
                ·
                  refine ⟨58301635991322710052763121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38867757327548473368508747 58301635991322710052763121)
                  ·
                    refine ⟨43726226993492032539572341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58301635991322710052763121 43726226993492032539572341)
                    ·
                      refine ⟨4099333780639878050584907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43726226993492032539572341 4099333780639878050584907)
                      ·
                        rfl

theorem cell23_7983424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_7983424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983424 prefixEnd_7983424 := by exact prefixLift 7983424
  have htrace : WordTrace (prefixWord ++ tailWord_7983424) baseStart_7983424 baseEnd_7983424 := by
    simpa [prefixWord, tailWord_7983424, baseEnd_7983424] using wordTrace_append hprefix tailTrace_7983424
  have hstable : (prefixWord ++ tailWord_7983424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983424).length < 2 ^ (prefixWord ++ tailWord_7983424).sum := by decide
  have hdescent : baseEnd_7983424 < baseStart_7983424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983545 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 2, 3, 2]
def baseStart_7983545 : Nat := 118140960795 + 7983545 * 2 ^ 59
def prefixEnd_7983545 : Nat := 4983230072969 + 3 ^ 40 * 7983545 * 2
def baseEnd_7983545 : Nat := 4099395911799072077171851

theorem tailTrace_7983545 : CollatzResearch.WordTrace tailWord_7983545 prefixEnd_7983545 4099395911799072077171851 := by
  unfold tailWord_7983545
  simp only [CollatzResearch.WordTrace]
  refine ⟨291183807861987420778848089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194122538574658280519232059 291183807861987420778848089)
  ·
    refine ⟨218387855896490565584136067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291183807861987420778848089 218387855896490565584136067)
    ·
      refine ⟨327581783844735848376204101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218387855896490565584136067 327581783844735848376204101)
      ·
        refine ⟨61421584470887971570538269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327581783844735848376204101 61421584470887971570538269)
        ·
          refine ⟨23033094176582989338951851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61421584470887971570538269 23033094176582989338951851)
          ·
            refine ⟨34549641264874484008427777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23033094176582989338951851 34549641264874484008427777)
            ·
              refine ⟨25912230948655863006320833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34549641264874484008427777 25912230948655863006320833)
              ·
                refine ⟨19434173211491897254740625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25912230948655863006320833 19434173211491897254740625)
                ·
                  refine ⟨14575629908618922941055469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19434173211491897254740625 14575629908618922941055469)
                  ·
                    refine ⟨5465861215732096102895801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14575629908618922941055469 5465861215732096102895801)
                    ·
                      refine ⟨4099395911799072077171851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465861215732096102895801 4099395911799072077171851)
                      ·
                        rfl

theorem cell23_7983545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_7983545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983545 prefixEnd_7983545 := by exact prefixLift 7983545
  have htrace : WordTrace (prefixWord ++ tailWord_7983545) baseStart_7983545 baseEnd_7983545 := by
    simpa [prefixWord, tailWord_7983545, baseEnd_7983545] using wordTrace_append hprefix tailTrace_7983545
  have hstable : (prefixWord ++ tailWord_7983545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983545).length < 2 ^ (prefixWord ++ tailWord_7983545).sum := by decide
  have hdescent : baseEnd_7983545 < baseStart_7983545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983561 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_7983561 : Nat := 118140960795 + 7983561 * 2 ^ 59
def prefixEnd_7983561 : Nat := 4983230072969 + 3 ^ 40 * 7983561 * 2
def baseEnd_7983561 : Nat := 4099404127489544014571777

theorem tailTrace_7983561 : CollatzResearch.WordTrace tailWord_7983561 prefixEnd_7983561 4099404127489544014571777 := by
  unfold tailWord_7983561
  simp only [CollatzResearch.WordTrace]
  refine ⟨291184391429929455511430537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194122927619952970340953691 291184391429929455511430537)
  ·
    refine ⟨218388293572447091633572903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291184391429929455511430537 218388293572447091633572903)
    ·
      refine ⟨327582440358670637450359355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218388293572447091633572903 327582440358670637450359355)
      ·
        refine ⟨491373660538005956175539033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327582440358670637450359355 491373660538005956175539033)
        ·
          refine ⟨368530245403504467131654275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491373660538005956175539033 368530245403504467131654275)
          ·
            refine ⟨552795368105256700697481413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368530245403504467131654275 552795368105256700697481413)
            ·
              refine ⟨103649131519735631380777765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 552795368105256700697481413 103649131519735631380777765)
              ·
                refine ⟨19434212159950430883895831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103649131519735631380777765 19434212159950430883895831)
                ·
                  refine ⟨29151318239925646325843747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19434212159950430883895831 29151318239925646325843747)
                  ·
                    refine ⟨43726977359888469488765621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29151318239925646325843747 43726977359888469488765621)
                    ·
                      refine ⟨4099404127489544014571777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43726977359888469488765621 4099404127489544014571777)
                      ·
                        rfl

theorem cell23_7983561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_7983561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983561 prefixEnd_7983561 := by exact prefixLift 7983561
  have htrace : WordTrace (prefixWord ++ tailWord_7983561) baseStart_7983561 baseEnd_7983561 := by
    simpa [prefixWord, tailWord_7983561, baseEnd_7983561] using wordTrace_append hprefix tailTrace_7983561
  have hstable : (prefixWord ++ tailWord_7983561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983561).length < 2 ^ (prefixWord ++ tailWord_7983561).sum := by decide
  have hdescent : baseEnd_7983561 < baseStart_7983561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983578 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_7983578 : Nat := 118140960795 + 7983578 * 2 ^ 59
def prefixEnd_7983578 : Nat := 4983230072969 + 3 ^ 40 * 7983578 * 2
def baseEnd_7983578 : Nat := 4099412856660670448059199

theorem tailTrace_7983578 : CollatzResearch.WordTrace tailWord_7983578 prefixEnd_7983578 4099412856660670448059199 := by
  unfold tailWord_7983578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72796252867716966853699847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194123340980578578276532925 72796252867716966853699847)
  ·
    refine ⟨109194379301575450280549771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72796252867716966853699847 109194379301575450280549771)
    ·
      refine ⟨163791568952363175420824657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109194379301575450280549771 163791568952363175420824657)
      ·
        refine ⟨122843676714272381565618493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163791568952363175420824657 122843676714272381565618493)
        ·
          refine ⟨46066378767852143087106935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122843676714272381565618493 46066378767852143087106935)
          ·
            refine ⟨69099568151778214630660403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46066378767852143087106935 69099568151778214630660403)
            ·
              refine ⟨103649352227667321945990605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69099568151778214630660403 103649352227667321945990605)
              ·
                refine ⟨38868507085375245729746477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103649352227667321945990605 38868507085375245729746477)
                ·
                  refine ⟨14575690157015717148654929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38868507085375245729746477 14575690157015717148654929)
                  ·
                    refine ⟨10931767617761787861491197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14575690157015717148654929 10931767617761787861491197)
                    ·
                      refine ⟨4099412856660670448059199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931767617761787861491197 4099412856660670448059199)
                      ·
                        rfl

theorem cell23_7983578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_7983578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983578 prefixEnd_7983578 := by exact prefixLift 7983578
  have htrace : WordTrace (prefixWord ++ tailWord_7983578) baseStart_7983578 baseEnd_7983578 := by
    simpa [prefixWord, tailWord_7983578, baseEnd_7983578] using wordTrace_append hprefix tailTrace_7983578
  have hstable : (prefixWord ++ tailWord_7983578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983578).length < 2 ^ (prefixWord ++ tailWord_7983578).sum := by decide
  have hdescent : baseEnd_7983578 < baseStart_7983578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983589 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_7983589 : Nat := 118140960795 + 7983589 * 2 ^ 59
def prefixEnd_7983589 : Nat := 4983230072969 + 3 ^ 40 * 7983589 * 2
def baseEnd_7983589 : Nat := 1366472834982623301673883

theorem tailTrace_7983589 : CollatzResearch.WordTrace tailWord_7983589 prefixEnd_7983589 1366472834982623301673883 := by
  unfold tailWord_7983589
  simp only [CollatzResearch.WordTrace]
  refine ⟨291185412673828016293449821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194123608449218677528966547 291185412673828016293449821)
  ·
    refine ⟨109194529752685506110043683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291185412673828016293449821 109194529752685506110043683)
    ·
      refine ⟨163791794629028259165065525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109194529752685506110043683 163791794629028259165065525)
      ·
        refine ⟨15355480746471399296724893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163791794629028259165065525 15355480746471399296724893)
        ·
          refine ⟨5758305279926774736271835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15355480746471399296724893 5758305279926774736271835)
          ·
            refine ⟨8637457919890162104407753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758305279926774736271835 8637457919890162104407753)
            ·
              refine ⟨6478093439917621578305815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637457919890162104407753 6478093439917621578305815)
              ·
                refine ⟨9717140159876432367458723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478093439917621578305815 9717140159876432367458723)
                ·
                  refine ⟨14575710239814648551188085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717140159876432367458723 14575710239814648551188085)
                  ·
                    refine ⟨1366472834982623301673883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14575710239814648551188085 1366472834982623301673883)
                    ·
                      rfl

theorem cell23_7983589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_7983589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983589 prefixEnd_7983589 := by exact prefixLift 7983589
  have htrace : WordTrace (prefixWord ++ tailWord_7983589) baseStart_7983589 baseEnd_7983589 := by
    simpa [prefixWord, tailWord_7983589, baseEnd_7983589] using wordTrace_append hprefix tailTrace_7983589
  have hstable : (prefixWord ++ tailWord_7983589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983589).length < 2 ^ (prefixWord ++ tailWord_7983589).sum := by decide
  have hdescent : baseEnd_7983589 < baseStart_7983589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983592 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7983592 : Nat := 118140960795 + 7983592 * 2 ^ 59
def prefixEnd_7983592 : Nat := 4983230072969 + 3 ^ 40 * 7983592 * 2
def baseEnd_7983592 : Nat := 4099420045389833393284135

theorem tailTrace_7983592 : CollatzResearch.WordTrace tailWord_7983592 prefixEnd_7983592 4099420045389833393284135 := by
  unfold tailWord_7983592
  simp only [CollatzResearch.WordTrace]
  refine ⟨145592761046408573902904515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194123681395211431870539353 145592761046408573902904515)
  ·
    refine ⟨218389141569612860854356773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145592761046408573902904515 218389141569612860854356773)
    ·
      refine ⟨40947964044302411410191895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218389141569612860854356773 40947964044302411410191895)
      ·
        refine ⟨61421946066453617115287843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40947964044302411410191895 61421946066453617115287843)
        ·
          refine ⟨92132919099680425672931765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61421946066453617115287843 92132919099680425672931765)
          ·
            refine ⟨8637461165595039906837353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92132919099680425672931765 8637461165595039906837353)
            ·
              refine ⟨6478095874196279930128015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637461165595039906837353 6478095874196279930128015)
              ·
                refine ⟨9717143811294419895192023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478095874196279930128015 9717143811294419895192023)
                ·
                  refine ⟨14575715716941629842788035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717143811294419895192023 14575715716941629842788035)
                  ·
                    refine ⟨21863573575412444764182053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14575715716941629842788035 21863573575412444764182053)
                    ·
                      refine ⟨4099420045389833393284135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21863573575412444764182053 4099420045389833393284135)
                      ·
                        rfl

theorem cell23_7983592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7983592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983592 prefixEnd_7983592 := by exact prefixLift 7983592
  have htrace : WordTrace (prefixWord ++ tailWord_7983592) baseStart_7983592 baseEnd_7983592 := by
    simpa [prefixWord, tailWord_7983592, baseEnd_7983592] using wordTrace_append hprefix tailTrace_7983592
  have hstable : (prefixWord ++ tailWord_7983592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983592).length < 2 ^ (prefixWord ++ tailWord_7983592).sum := by decide
  have hdescent : baseEnd_7983592 < baseStart_7983592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983629 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7983629 : Nat := 118140960795 + 7983629 * 2 ^ 59
def prefixEnd_7983629 : Nat := 4983230072969 + 3 ^ 40 * 7983629 * 2
def baseEnd_7983629 : Nat := 4099439044174049748521465

theorem tailTrace_7983629 : CollatzResearch.WordTrace tailWord_7983629 prefixEnd_7983629 4099439044174049748521465 := by
  unfold tailWord_7983629
  simp only [CollatzResearch.WordTrace]
  refine ⟨291186871593683103124905941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194124581062455402083270627 291186871593683103124905941)
  ·
    refine ⟨6824692302976947729489983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 291186871593683103124905941 6824692302976947729489983)
    ·
      refine ⟨10237038454465421594234975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824692302976947729489983 10237038454465421594234975)
      ·
        refine ⟨15355557681698132391352463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10237038454465421594234975 15355557681698132391352463)
        ·
          refine ⟨23033336522547198587028695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355557681698132391352463 23033336522547198587028695)
          ·
            refine ⟨34550004783820797880543043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23033336522547198587028695 34550004783820797880543043)
            ·
              refine ⟨51825007175731196820814565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34550004783820797880543043 51825007175731196820814565)
              ·
                refine ⟨9717188845449599403902731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51825007175731196820814565 9717188845449599403902731)
                ·
                  refine ⟨14575783268174399105854097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717188845449599403902731 14575783268174399105854097)
                  ·
                    refine ⟨10931837451130799329390573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14575783268174399105854097 10931837451130799329390573)
                    ·
                      refine ⟨4099439044174049748521465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10931837451130799329390573 4099439044174049748521465)
                      ·
                        rfl

theorem cell23_7983629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7983629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983629 prefixEnd_7983629 := by exact prefixLift 7983629
  have htrace : WordTrace (prefixWord ++ tailWord_7983629) baseStart_7983629 baseEnd_7983629 := by
    simpa [prefixWord, tailWord_7983629, baseEnd_7983629] using wordTrace_append hprefix tailTrace_7983629
  have hstable : (prefixWord ++ tailWord_7983629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983629).length < 2 ^ (prefixWord ++ tailWord_7983629).sum := by decide
  have hdescent : baseEnd_7983629 < baseStart_7983629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983631 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_7983631 : Nat := 118140960795 + 7983631 * 2 ^ 59
def prefixEnd_7983631 : Nat := 4983230072969 + 3 ^ 40 * 7983631 * 2
def baseEnd_7983631 : Nat := 4099440071135358740696455

theorem tailTrace_7983631 : CollatzResearch.WordTrace tailWord_7983631 prefixEnd_7983631 4099440071135358740696455 := by
  unfold tailWord_7983631
  simp only [CollatzResearch.WordTrace]
  refine ⟨291186944539675857466478747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194124629693117238310985831 291186944539675857466478747)
  ·
    refine ⟨436780416809513786199718121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291186944539675857466478747 436780416809513786199718121)
    ·
      refine ⟨327585312607135339649788591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436780416809513786199718121 327585312607135339649788591)
      ·
        refine ⟨491377968910703009474682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327585312607135339649788591 491377968910703009474682887)
        ·
          refine ⟨737066953366054514212024331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491377968910703009474682887 737066953366054514212024331)
          ·
            refine ⟨1105600430049081771318036497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737066953366054514212024331 1105600430049081771318036497)
            ·
              refine ⟨829200322536811328488527373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105600430049081771318036497 829200322536811328488527373)
              ·
                refine ⟨310950120951304248183197765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829200322536811328488527373 310950120951304248183197765)
                ·
                  refine ⟨58303147678369546534349581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310950120951304248183197765 58303147678369546534349581)
                  ·
                    refine ⟨21863680379388579950381093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58303147678369546534349581 21863680379388579950381093)
                    ·
                      refine ⟨4099440071135358740696455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21863680379388579950381093 4099440071135358740696455)
                      ·
                        rfl

theorem cell23_7983631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_7983631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983631 prefixEnd_7983631 := by exact prefixLift 7983631
  have htrace : WordTrace (prefixWord ++ tailWord_7983631) baseStart_7983631 baseEnd_7983631 := by
    simpa [prefixWord, tailWord_7983631, baseEnd_7983631] using wordTrace_append hprefix tailTrace_7983631
  have hstable : (prefixWord ++ tailWord_7983631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983631).length < 2 ^ (prefixWord ++ tailWord_7983631).sum := by decide
  have hdescent : baseEnd_7983631 < baseStart_7983631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983686 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7983686 : Nat := 118140960795 + 7983686 * 2 ^ 59
def prefixEnd_7983686 : Nat := 4983230072969 + 3 ^ 40 * 7983686 * 2
def baseEnd_7983686 : Nat := 4099468312571356025508703

theorem tailTrace_7983686 : CollatzResearch.WordTrace tailWord_7983686 prefixEnd_7983686 4099468312571356025508703 := by
  unfold tailWord_7983686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099654704827393808116591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194125967036317734573153941 9099654704827393808116591)
  ·
    refine ⟨13649482057241090712174887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099654704827393808116591 13649482057241090712174887)
    ·
      refine ⟨20474223085861636068262331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13649482057241090712174887 20474223085861636068262331)
      ·
        refine ⟨30711334628792454102393497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20474223085861636068262331 30711334628792454102393497)
        ·
          refine ⟨23033500971594340576795123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30711334628792454102393497 23033500971594340576795123)
          ·
            refine ⟨34550251457391510865192685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23033500971594340576795123 34550251457391510865192685)
            ·
              refine ⟨12956344296521816574447257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34550251457391510865192685 12956344296521816574447257)
              ·
                refine ⟨9717258222391362430835443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12956344296521816574447257 9717258222391362430835443)
                ·
                  refine ⟨14575887333587043646253165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717258222391362430835443 14575887333587043646253165)
                  ·
                    refine ⟨5465957750095141367344937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14575887333587043646253165 5465957750095141367344937)
                    ·
                      refine ⟨4099468312571356025508703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5465957750095141367344937 4099468312571356025508703)
                      ·
                        rfl

theorem cell23_7983686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7983686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983686 prefixEnd_7983686 := by exact prefixLift 7983686
  have htrace : WordTrace (prefixWord ++ tailWord_7983686) baseStart_7983686 baseEnd_7983686 := by
    simpa [prefixWord, tailWord_7983686, baseEnd_7983686] using wordTrace_append hprefix tailTrace_7983686
  have hstable : (prefixWord ++ tailWord_7983686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983686).length < 2 ^ (prefixWord ++ tailWord_7983686).sum := by decide
  have hdescent : baseEnd_7983686 < baseStart_7983686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983768 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7983768 : Nat := 118140960795 + 7983768 * 2 ^ 59
def prefixEnd_7983768 : Nat := 4983230072969 + 3 ^ 40 * 7983768 * 2
def baseEnd_7983768 : Nat := 4099510417985024704683325

theorem tailTrace_7983768 : CollatzResearch.WordTrace tailWord_7983768 prefixEnd_7983768 4099510417985024704683325 := by
  unfold tailWord_7983768
  simp only [CollatzResearch.WordTrace]
  refine ⟨145595970670089764932107979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194127960893453019909477305 145595970670089764932107979)
  ·
    refine ⟨218393956005134647398161969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145595970670089764932107979 218393956005134647398161969)
    ·
      refine ⟨163795467003850985548621477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218393956005134647398161969 163795467003850985548621477)
      ·
        refine ⟨30711650063222059790366527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163795467003850985548621477 30711650063222059790366527)
        ·
          refine ⟨46067475094833089685549791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30711650063222059790366527 46067475094833089685549791)
          ·
            refine ⟨69101212642249634528324687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46067475094833089685549791 69101212642249634528324687)
            ·
              refine ⟨103651818963374451792487031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69101212642249634528324687 103651818963374451792487031)
              ·
                refine ⟨155477728445061677688730547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103651818963374451792487031 155477728445061677688730547)
                ·
                  refine ⟨233216592667592516533095821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155477728445061677688730547 233216592667592516533095821)
                  ·
                    refine ⟨87456222250347193699910933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233216592667592516533095821 87456222250347193699910933)
                    ·
                      refine ⟨4099510417985024704683325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87456222250347193699910933 4099510417985024704683325)
                      ·
                        rfl

theorem cell23_7983768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7983768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983768 prefixEnd_7983768 := by exact prefixLift 7983768
  have htrace : WordTrace (prefixWord ++ tailWord_7983768) baseStart_7983768 baseEnd_7983768 := by
    simpa [prefixWord, tailWord_7983768, baseEnd_7983768] using wordTrace_append hprefix tailTrace_7983768
  have hstable : (prefixWord ++ tailWord_7983768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983768).length < 2 ^ (prefixWord ++ tailWord_7983768).sum := by decide
  have hdescent : baseEnd_7983768 < baseStart_7983768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983772 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7983772 : Nat := 118140960795 + 7983772 * 2 ^ 59
def prefixEnd_7983772 : Nat := 4983230072969 + 3 ^ 40 * 7983772 * 2
def baseEnd_7983772 : Nat := 4099512471907642689033307

theorem tailTrace_7983772 : CollatzResearch.WordTrace tailWord_7983772 prefixEnd_7983772 4099512471907642689033307 := by
  unfold tailWord_7983772
  simp only [CollatzResearch.WordTrace]
  refine ⟨145596043616082519273680785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194128058154776692364907713 145596043616082519273680785)
  ·
    refine ⟨109197032712061889455260589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145596043616082519273680785 109197032712061889455260589)
    ·
      refine ⟨40948887267023208545722721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109197032712061889455260589 40948887267023208545722721)
      ·
        refine ⟨30711665450267406409292041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40948887267023208545722721 30711665450267406409292041)
        ·
          refine ⟨23033749087700554806969031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30711665450267406409292041 23033749087700554806969031)
          ·
            refine ⟨34550623631550832210453547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23033749087700554806969031 34550623631550832210453547)
            ·
              refine ⟨51825935447326248315680321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34550623631550832210453547 51825935447326248315680321)
              ·
                refine ⟨38869451585494686236760241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51825935447326248315680321 38869451585494686236760241)
                ·
                  refine ⟨29152088689121014677570181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38869451585494686236760241 29152088689121014677570181)
                  ·
                    refine ⟨5466016629210190252044409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29152088689121014677570181 5466016629210190252044409)
                    ·
                      refine ⟨4099512471907642689033307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466016629210190252044409 4099512471907642689033307)
                      ·
                        rfl

theorem cell23_7983772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7983772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983772 prefixEnd_7983772 := by exact prefixLift 7983772
  have htrace : WordTrace (prefixWord ++ tailWord_7983772) baseStart_7983772 baseEnd_7983772 := by
    simpa [prefixWord, tailWord_7983772, baseEnd_7983772] using wordTrace_append hprefix tailTrace_7983772
  have hstable : (prefixWord ++ tailWord_7983772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983772).length < 2 ^ (prefixWord ++ tailWord_7983772).sum := by decide
  have hdescent : baseEnd_7983772 < baseStart_7983772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983825 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_7983825 : Nat := 118140960795 + 7983825 * 2 ^ 59
def prefixEnd_7983825 : Nat := 4983230072969 + 3 ^ 40 * 7983825 * 2
def baseEnd_7983825 : Nat := 1366513228794110327223521

theorem tailTrace_7983825 : CollatzResearch.WordTrace tailWord_7983825 prefixEnd_7983825 1366513228794110327223521 := by
  unfold tailWord_7983825
  simp only [CollatzResearch.WordTrace]
  refine ⟨291194020300973028599040929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194129346867315352399360619 291194020300973028599040929)
  ·
    refine ⟨218395515225729771449280697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291194020300973028599040929 218395515225729771449280697)
    ·
      refine ⟨163796636419297328586960523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218395515225729771449280697 163796636419297328586960523)
      ·
        refine ⟨245694954628945992880440785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163796636419297328586960523 245694954628945992880440785)
        ·
          refine ⟨184271215971709494660330589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245694954628945992880440785 184271215971709494660330589)
          ·
            refine ⟨69101705989391060497623971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184271215971709494660330589 69101705989391060497623971)
            ·
              refine ⟨103652558984086590746435957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69101705989391060497623971 103652558984086590746435957)
              ·
                refine ⟨9717427404758117882478371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103652558984086590746435957 9717427404758117882478371)
                ·
                  refine ⟨14576141107137176823717557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717427404758117882478371 14576141107137176823717557)
                  ·
                    refine ⟨1366513228794110327223521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14576141107137176823717557 1366513228794110327223521)
                    ·
                      rfl

theorem cell23_7983825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_7983825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983825 prefixEnd_7983825 := by exact prefixLift 7983825
  have htrace : WordTrace (prefixWord ++ tailWord_7983825) baseStart_7983825 baseEnd_7983825 := by
    simpa [prefixWord, tailWord_7983825, baseEnd_7983825] using wordTrace_append hprefix tailTrace_7983825
  have hstable : (prefixWord ++ tailWord_7983825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983825).length < 2 ^ (prefixWord ++ tailWord_7983825).sum := by decide
  have hdescent : baseEnd_7983825 < baseStart_7983825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983832 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_7983832 : Nat := 118140960795 + 7983832 * 2 ^ 59
def prefixEnd_7983832 : Nat := 4983230072969 + 3 ^ 40 * 7983832 * 2
def baseEnd_7983832 : Nat := 4099543280746912454283031

theorem tailTrace_7983832 : CollatzResearch.WordTrace tailWord_7983832 prefixEnd_7983832 4099543280746912454283031 := by
  unfold tailWord_7983832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145597137805973834397272875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194129517074631779196363833 145597137805973834397272875)
  ·
    refine ⟨218395706708960751595909313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145597137805973834397272875 218395706708960751595909313)
    ·
      refine ⟨163796780031720563696931985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218395706708960751595909313 163796780031720563696931985)
      ·
        refine ⟨122847585023790422772698989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163796780031720563696931985 122847585023790422772698989)
        ·
          refine ⟨46067844383921408539762121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122847585023790422772698989 46067844383921408539762121)
          ·
            refine ⟨34550883287941056404821591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46067844383921408539762121 34550883287941056404821591)
            ·
              refine ⟨51826324931911584607232387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34550883287941056404821591 51826324931911584607232387)
              ·
                refine ⟨77739487397867376910848581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51826324931911584607232387 77739487397867376910848581)
                ·
                  refine ⟨14576153887100133170784109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77739487397867376910848581 14576153887100133170784109)
                  ·
                    refine ⟨5466057707662549939044041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14576153887100133170784109 5466057707662549939044041)
                    ·
                      refine ⟨4099543280746912454283031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466057707662549939044041 4099543280746912454283031)
                      ·
                        rfl

theorem cell23_7983832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_7983832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983832 prefixEnd_7983832 := by exact prefixLift 7983832
  have htrace : WordTrace (prefixWord ++ tailWord_7983832) baseStart_7983832 baseEnd_7983832 := by
    simpa [prefixWord, tailWord_7983832, baseEnd_7983832] using wordTrace_append hprefix tailTrace_7983832
  have hstable : (prefixWord ++ tailWord_7983832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983832).length < 2 ^ (prefixWord ++ tailWord_7983832).sum := by decide
  have hdescent : baseEnd_7983832 < baseStart_7983832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983839 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_7983839 : Nat := 118140960795 + 7983839 * 2 ^ 59
def prefixEnd_7983839 : Nat := 4983230072969 + 3 ^ 40 * 7983839 * 2
def baseEnd_7983839 : Nat := 4099546875111493926895499

theorem tailTrace_7983839 : CollatzResearch.WordTrace tailWord_7983839 prefixEnd_7983839 4099546875111493926895499 := by
  unfold tailWord_7983839
  simp only [CollatzResearch.WordTrace]
  refine ⟨291194530922922308990050571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194129687281948205993367047 291194530922922308990050571)
  ·
    refine ⟨436791796384383463485075857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291194530922922308990050571 436791796384383463485075857)
    ·
      refine ⟨327593847288287597613806893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436791796384383463485075857 327593847288287597613806893)
      ·
        refine ⟨122847692733107849105177585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327593847288287597613806893 122847692733107849105177585)
        ·
          refine ⟨92135769549830886828883189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122847692733107849105177585 92135769549830886828883189)
          ·
            refine ⟨8637728395296645640207799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92135769549830886828883189 8637728395296645640207799)
            ·
              refine ⟨12956592592944968460311699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637728395296645640207799 12956592592944968460311699)
              ·
                refine ⟨19434888889417452690467549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12956592592944968460311699 19434888889417452690467549)
                ·
                  refine ⟨7288083333531544758925331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19434888889417452690467549 7288083333531544758925331)
                  ·
                    refine ⟨10932125000297317138387997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288083333531544758925331 10932125000297317138387997)
                    ·
                      refine ⟨4099546875111493926895499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932125000297317138387997 4099546875111493926895499)
                      ·
                        rfl

theorem cell23_7983839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_7983839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983839 prefixEnd_7983839 := by exact prefixLift 7983839
  have htrace : WordTrace (prefixWord ++ tailWord_7983839) baseStart_7983839 baseEnd_7983839 := by
    simpa [prefixWord, tailWord_7983839, baseEnd_7983839] using wordTrace_append hprefix tailTrace_7983839
  have hstable : (prefixWord ++ tailWord_7983839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983839).length < 2 ^ (prefixWord ++ tailWord_7983839).sum := by decide
  have hdescent : baseEnd_7983839 < baseStart_7983839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983862 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7983862 : Nat := 118140960795 + 7983862 * 2 ^ 59
def prefixEnd_7983862 : Nat := 4983230072969 + 3 ^ 40 * 7983862 * 2
def baseEnd_7983862 : Nat := 4099558685166547336907893

theorem tailTrace_7983862 : CollatzResearch.WordTrace tailWord_7983862 prefixEnd_7983862 4099558685166547336907893 := by
  unfold tailWord_7983862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199710612614936494883615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194130246534559322612091893 18199710612614936494883615)
  ·
    refine ⟨27299565918922404742325423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18199710612614936494883615 27299565918922404742325423)
    ·
      refine ⟨40949348878383607113488135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27299565918922404742325423 40949348878383607113488135)
      ·
        refine ⟨61424023317575410670232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40949348878383607113488135 61424023317575410670232203)
        ·
          refine ⟨92136034976363116005348305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61424023317575410670232203 92136034976363116005348305)
          ·
            refine ⟨69102026232272337004011229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92136034976363116005348305 69102026232272337004011229)
            ·
              refine ⟨25913259837102126376504211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69102026232272337004011229 25913259837102126376504211)
              ·
                refine ⟨38869889755653189564756317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25913259837102126376504211 38869889755653189564756317)
                ·
                  refine ⟨14576208658369946086783619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38869889755653189564756317 14576208658369946086783619)
                  ·
                    refine ⟨21864312987554919130175429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14576208658369946086783619 21864312987554919130175429)
                    ·
                      refine ⟨4099558685166547336907893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21864312987554919130175429 4099558685166547336907893)
                      ·
                        rfl

theorem cell23_7983862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7983862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983862 prefixEnd_7983862 := by exact prefixLift 7983862
  have htrace : WordTrace (prefixWord ++ tailWord_7983862) baseStart_7983862 baseEnd_7983862 := by
    simpa [prefixWord, tailWord_7983862, baseEnd_7983862] using wordTrace_append hprefix tailTrace_7983862
  have hstable : (prefixWord ++ tailWord_7983862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983862).length < 2 ^ (prefixWord ++ tailWord_7983862).sum := by decide
  have hdescent : baseEnd_7983862 < baseStart_7983862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983888 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_7983888 : Nat := 118140960795 + 7983888 * 2 ^ 59
def prefixEnd_7983888 : Nat := 4983230072969 + 3 ^ 40 * 7983888 * 2
def baseEnd_7983888 : Nat := 4099572035663564235182773

theorem tailTrace_7983888 : CollatzResearch.WordTrace tailWord_7983888 prefixEnd_7983888 4099572035663564235182773 := by
  unfold tailWord_7983888
  simp only [CollatzResearch.WordTrace]
  refine ⟨145598159049872395179292159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194130878733163193572389545 145598159049872395179292159)
  ·
    refine ⟨218397238574808592768938239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145598159049872395179292159 218397238574808592768938239)
    ·
      refine ⟨327595857862212889153407359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218397238574808592768938239 327595857862212889153407359)
      ·
        refine ⟨491393786793319333730111039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327595857862212889153407359 491393786793319333730111039)
        ·
          refine ⟨737090680189979000595166559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491393786793319333730111039 737090680189979000595166559)
          ·
            refine ⟨1105636020284968500892749839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737090680189979000595166559 1105636020284968500892749839)
            ·
              refine ⟨1658454030427452751339124759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105636020284968500892749839 1658454030427452751339124759)
              ·
                refine ⟨2487681045641179127008687139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658454030427452751339124759 2487681045641179127008687139)
                ·
                  refine ⟨3731521568461768690513030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487681045641179127008687139 3731521568461768690513030709)
                  ·
                    refine ⟨349830147043290814735596629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3731521568461768690513030709 349830147043290814735596629)
                    ·
                      refine ⟨4099572035663564235182773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349830147043290814735596629 4099572035663564235182773)
                      ·
                        rfl

theorem cell23_7983888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_7983888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983888 prefixEnd_7983888 := by exact prefixLift 7983888
  have htrace : WordTrace (prefixWord ++ tailWord_7983888) baseStart_7983888 baseEnd_7983888 := by
    simpa [prefixWord, tailWord_7983888, baseEnd_7983888] using wordTrace_append hprefix tailTrace_7983888
  have hstable : (prefixWord ++ tailWord_7983888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983888).length < 2 ^ (prefixWord ++ tailWord_7983888).sum := by decide
  have hdescent : baseEnd_7983888 < baseStart_7983888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983933 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7983933 : Nat := 118140960795 + 7983933 * 2 ^ 59
def prefixEnd_7983933 : Nat := 4983230072969 + 3 ^ 40 * 7983933 * 2
def baseEnd_7983933 : Nat := 4099595142293016559120067

theorem tailTrace_7983933 : CollatzResearch.WordTrace tailWord_7983933 prefixEnd_7983933 4099595142293016559120067 := by
  unfold tailWord_7983933
  simp only [CollatzResearch.WordTrace]
  refine ⟨291197959384581763043972453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194131972923054508695981635 291197959384581763043972453)
  ·
    refine ⟨54599617384609080570744835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291197959384581763043972453 54599617384609080570744835)
    ·
      refine ⟨81899426076913620856117253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54599617384609080570744835 81899426076913620856117253)
      ·
        refine ⟨15356142389421303910521985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81899426076913620856117253 15356142389421303910521985)
        ·
          refine ⟨11517106792065977932891489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15356142389421303910521985 11517106792065977932891489)
          ·
            refine ⟨8637830094049483449668617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11517106792065977932891489 8637830094049483449668617)
            ·
              refine ⟨6478372570537112587251463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637830094049483449668617 6478372570537112587251463)
              ·
                refine ⟨9717558855805668880877195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478372570537112587251463 9717558855805668880877195)
                ·
                  refine ⟨14576338283708503321315793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717558855805668880877195 14576338283708503321315793)
                  ·
                    refine ⟨10932253712781377490986845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14576338283708503321315793 10932253712781377490986845)
                    ·
                      refine ⟨4099595142293016559120067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932253712781377490986845 4099595142293016559120067)
                      ·
                        rfl

theorem cell23_7983933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7983933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983933 prefixEnd_7983933 := by exact prefixLift 7983933
  have htrace : WordTrace (prefixWord ++ tailWord_7983933) baseStart_7983933 baseEnd_7983933 := by
    simpa [prefixWord, tailWord_7983933, baseEnd_7983933] using wordTrace_append hprefix tailTrace_7983933
  have hstable : (prefixWord ++ tailWord_7983933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983933).length < 2 ^ (prefixWord ++ tailWord_7983933).sum := by decide
  have hdescent : baseEnd_7983933 < baseStart_7983933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983939 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 1, 3, 2]
def baseStart_7983939 : Nat := 118140960795 + 7983939 * 2 ^ 59
def prefixEnd_7983939 : Nat := 4983230072969 + 3 ^ 40 * 7983939 * 2
def baseEnd_7983939 : Nat := 4099598223176943535645039

theorem tailTrace_7983939 : CollatzResearch.WordTrace tailWord_7983939 prefixEnd_7983939 4099598223176943535645039 := by
  unfold tailWord_7983939
  simp only [CollatzResearch.WordTrace]
  refine ⟨291198178222560026068690871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194132118815040017379127247 291198178222560026068690871)
  ·
    refine ⟨436797267333840039103036307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291198178222560026068690871 436797267333840039103036307)
    ·
      refine ⟨655195901000760058654554461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436797267333840039103036307 655195901000760058654554461)
      ·
        refine ⟨245698462875285021995457923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655195901000760058654554461 245698462875285021995457923)
        ·
          refine ⟨368547694312927532993186885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245698462875285021995457923 368547694312927532993186885)
          ·
            refine ⟨69102692683673912436222541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368547694312927532993186885 69102692683673912436222541)
            ·
              refine ⟨25913509756377717163583453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69102692683673912436222541 25913509756377717163583453)
              ·
                refine ⟨9717566158641643936343795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25913509756377717163583453 9717566158641643936343795)
                ·
                  refine ⟨14576349237962465904515693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717566158641643936343795 14576349237962465904515693)
                  ·
                    refine ⟨5466130964235924714193385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14576349237962465904515693 5466130964235924714193385)
                    ·
                      refine ⟨4099598223176943535645039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466130964235924714193385 4099598223176943535645039)
                      ·
                        rfl

theorem cell23_7983939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_7983939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983939 prefixEnd_7983939 := by exact prefixLift 7983939
  have htrace : WordTrace (prefixWord ++ tailWord_7983939) baseStart_7983939 baseEnd_7983939 := by
    simpa [prefixWord, tailWord_7983939, baseEnd_7983939] using wordTrace_append hprefix tailTrace_7983939
  have hstable : (prefixWord ++ tailWord_7983939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983939).length < 2 ^ (prefixWord ++ tailWord_7983939).sum := by decide
  have hdescent : baseEnd_7983939 < baseStart_7983939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983940 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7983940 : Nat := 118140960795 + 7983940 * 2 ^ 59
def prefixEnd_7983940 : Nat := 4983230072969 + 3 ^ 40 * 7983940 * 2
def baseEnd_7983940 : Nat := 1366532912219199343910845

theorem tailTrace_7983940 : CollatzResearch.WordTrace tailWord_7983940 prefixEnd_7983940 1366532912219199343910845 := by
  unfold tailWord_7983940
  simp only [CollatzResearch.WordTrace]
  refine ⟨145599107347778201619738637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194132143130370935492984849 145599107347778201619738637)
  ·
    refine ⟨54599665255416825607401989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145599107347778201619738637 54599665255416825607401989)
    ·
      refine ⟨10237437235390654801387873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54599665255416825607401989 10237437235390654801387873)
      ·
        refine ⟨7678077926542991101040905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10237437235390654801387873 7678077926542991101040905)
        ·
          refine ⟨5758558444907243325780679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7678077926542991101040905 5758558444907243325780679)
          ·
            refine ⟨8637837667360864988671019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758558444907243325780679 8637837667360864988671019)
            ·
              refine ⟨12956756501041297483006529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637837667360864988671019 12956756501041297483006529)
              ·
                refine ⟨9717567375780973112254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12956756501041297483006529 9717567375780973112254897)
                ·
                  refine ⟨7288175531835729834191173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717567375780973112254897 7288175531835729834191173)
                  ·
                    refine ⟨1366532912219199343910845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288175531835729834191173 1366532912219199343910845)
                    ·
                      rfl

theorem cell23_7983940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7983940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983940 prefixEnd_7983940 := by exact prefixLift 7983940
  have htrace : WordTrace (prefixWord ++ tailWord_7983940) baseStart_7983940 baseEnd_7983940 := by
    simpa [prefixWord, tailWord_7983940, baseEnd_7983940] using wordTrace_append hprefix tailTrace_7983940
  have hstable : (prefixWord ++ tailWord_7983940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983940).length < 2 ^ (prefixWord ++ tailWord_7983940).sum := by decide
  have hdescent : baseEnd_7983940 < baseStart_7983940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983945 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_7983945 : Nat := 118140960795 + 7983945 * 2 ^ 59
def prefixEnd_7983945 : Nat := 4983230072969 + 3 ^ 40 * 7983945 * 2
def baseEnd_7983945 : Nat := 1366533768020290170723337

theorem tailTrace_7983945 : CollatzResearch.WordTrace tailWord_7983945 prefixEnd_7983945 1366533768020290170723337 := by
  unfold tailWord_7983945
  simp only [CollatzResearch.WordTrace]
  refine ⟨291198397060538289093409289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194132264707025526062272859 291198397060538289093409289)
  ·
    refine ⟨218398797795403716820056967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291198397060538289093409289 218398797795403716820056967)
    ·
      refine ⟨327598196693105575230085451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218398797795403716820056967 327598196693105575230085451)
      ·
        refine ⟨491397295039658362845128177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327598196693105575230085451 491397295039658362845128177)
        ·
          refine ⟨368547971279743772133846133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491397295039658362845128177 368547971279743772133846133)
          ·
            refine ⟨34551372307475978637548075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368547971279743772133846133 34551372307475978637548075)
            ·
              refine ⟨51827058461213967956322113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34551372307475978637548075 51827058461213967956322113)
              ·
                refine ⟨38870293845910475967241585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51827058461213967956322113 38870293845910475967241585)
                ·
                  refine ⟨29152720384432856975431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38870293845910475967241585 29152720384432856975431189)
                  ·
                    refine ⟨1366533768020290170723337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29152720384432856975431189 1366533768020290170723337)
                    ·
                      rfl

theorem cell23_7983945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_7983945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983945 prefixEnd_7983945 := by exact prefixLift 7983945
  have htrace : WordTrace (prefixWord ++ tailWord_7983945) baseStart_7983945 baseEnd_7983945 := by
    simpa [prefixWord, tailWord_7983945, baseEnd_7983945] using wordTrace_append hprefix tailTrace_7983945
  have hstable : (prefixWord ++ tailWord_7983945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983945).length < 2 ^ (prefixWord ++ tailWord_7983945).sum := by decide
  have hdescent : baseEnd_7983945 < baseStart_7983945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983952 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2]
def baseStart_7983952 : Nat := 118140960795 + 7983952 * 2 ^ 59
def prefixEnd_7983952 : Nat := 4983230072969 + 3 ^ 40 * 7983952 * 2
def baseEnd_7983952 : Nat := 4099604898425451984782479

theorem tailTrace_7983952 : CollatzResearch.WordTrace tailWord_7983952 prefixEnd_7983952 4099604898425451984782479 := by
  unfold tailWord_7983952
  simp only [CollatzResearch.WordTrace]
  refine ⟨145599326185756464644457055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194132434914341952859276073 145599326185756464644457055)
  ·
    refine ⟨218398989278634696966685583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145599326185756464644457055 218398989278634696966685583)
    ·
      refine ⟨327598483917952045450028375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218398989278634696966685583 327598483917952045450028375)
      ·
        refine ⟨491397725876928068175042563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327598483917952045450028375 491397725876928068175042563)
        ·
          refine ⟨737096588815392102262563845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491397725876928068175042563 737096588815392102262563845)
          ·
            refine ⟨138205610402886019174230721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 737096588815392102262563845 138205610402886019174230721)
            ·
              refine ⟨103654207802164514380673041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138205610402886019174230721 103654207802164514380673041)
              ·
                refine ⟨77740655851623385785504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103654207802164514380673041 77740655851623385785504781)
                ·
                  refine ⟨29152745944358769669564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77740655851623385785504781 29152745944358769669564293)
                  ·
                    refine ⟨5466139864567269313043305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29152745944358769669564293 5466139864567269313043305)
                    ·
                      refine ⟨4099604898425451984782479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466139864567269313043305 4099604898425451984782479)
                      ·
                        rfl

theorem cell23_7983952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 4, 2].length) (baseStart_7983952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983952 prefixEnd_7983952 := by exact prefixLift 7983952
  have htrace : WordTrace (prefixWord ++ tailWord_7983952) baseStart_7983952 baseEnd_7983952 := by
    simpa [prefixWord, tailWord_7983952, baseEnd_7983952] using wordTrace_append hprefix tailTrace_7983952
  have hstable : (prefixWord ++ tailWord_7983952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983952).length < 2 ^ (prefixWord ++ tailWord_7983952).sum := by decide
  have hdescent : baseEnd_7983952 < baseStart_7983952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3]
def baseStart_7983955 : Nat := 118140960795 + 7983955 * 2 ^ 59
def prefixEnd_7983955 : Nat := 4983230072969 + 3 ^ 40 * 7983955 * 2
def baseEnd_7983955 : Nat := 4099606438867415473044965

theorem tailTrace_7983955 : CollatzResearch.WordTrace tailWord_7983955 prefixEnd_7983955 4099606438867415473044965 := by
  unfold tailWord_7983955
  simp only [CollatzResearch.WordTrace]
  refine ⟨291198761790502060801273319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194132507860334707200848879 291198761790502060801273319)
  ·
    refine ⟨436798142685753091201909979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291198761790502060801273319 436798142685753091201909979)
    ·
      refine ⟨655197214028629636802864969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436798142685753091201909979 655197214028629636802864969)
      ·
        refine ⟨491397910521472227602148727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655197214028629636802864969 491397910521472227602148727)
        ·
          refine ⟨737096865782208341403223091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491397910521472227602148727 737096865782208341403223091)
          ·
            refine ⟨1105645298673312512104834637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737096865782208341403223091 1105645298673312512104834637)
            ·
              refine ⟨414616987002492192039312989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105645298673312512104834637 414616987002492192039312989)
              ·
                refine ⟨155481370125934572014742371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414616987002492192039312989 155481370125934572014742371)
                ·
                  refine ⟨233222055188901858022113557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155481370125934572014742371 233222055188901858022113557)
                  ·
                    refine ⟨10932283836979774594786573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 233222055188901858022113557 10932283836979774594786573)
                    ·
                      refine ⟨4099606438867415473044965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932283836979774594786573 4099606438867415473044965)
                      ·
                        rfl

theorem cell23_7983955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_7983955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983955 prefixEnd_7983955 := by exact prefixLift 7983955
  have htrace : WordTrace (prefixWord ++ tailWord_7983955) baseStart_7983955 baseEnd_7983955 := by
    simpa [prefixWord, tailWord_7983955, baseEnd_7983955] using wordTrace_append hprefix tailTrace_7983955
  have hstable : (prefixWord ++ tailWord_7983955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983955).length < 2 ^ (prefixWord ++ tailWord_7983955).sum := by decide
  have hdescent : baseEnd_7983955 < baseStart_7983955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7983992 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 5]
def baseStart_7983992 : Nat := 118140960795 + 7983992 * 2 ^ 59
def prefixEnd_7983992 : Nat := 4983230072969 + 3 ^ 40 * 7983992 * 2
def baseEnd_7983992 : Nat := 455513937516847980920255

theorem tailTrace_7983992 : CollatzResearch.WordTrace tailWord_7983992 prefixEnd_7983992 455513937516847980920255 := by
  unfold tailWord_7983992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145600055645684008060185115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194133407527578677413580153 145600055645684008060185115)
  ·
    refine ⟨218400083468526012090277673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145600055645684008060185115 218400083468526012090277673)
    ·
      refine ⟨163800062601394509067708255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218400083468526012090277673 163800062601394509067708255)
      ·
        refine ⟨245700093902091763601562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163800062601394509067708255 245700093902091763601562383)
        ·
          refine ⟨368550140853137645402343575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245700093902091763601562383 368550140853137645402343575)
          ·
            refine ⟨552825211279706468103515363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368550140853137645402343575 552825211279706468103515363)
            ·
              refine ⟨829237816919559702155273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552825211279706468103515363 829237816919559702155273045)
              ·
                refine ⟨4858815333513045129816053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 829237816919559702155273045 4858815333513045129816053)
                ·
                  refine ⟨455513937516847980920255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858815333513045129816053 455513937516847980920255)
                  ·
                    rfl

theorem cell23_7983992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 5].length) (baseStart_7983992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7983992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7983992 prefixEnd_7983992 := by exact prefixLift 7983992
  have htrace : WordTrace (prefixWord ++ tailWord_7983992) baseStart_7983992 baseEnd_7983992 := by
    simpa [prefixWord, tailWord_7983992, baseEnd_7983992] using wordTrace_append hprefix tailTrace_7983992
  have hstable : (prefixWord ++ tailWord_7983992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7983992).length < 2 ^ (prefixWord ++ tailWord_7983992).sum := by decide
  have hdescent : baseEnd_7983992 < baseStart_7983992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7983992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984035 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 8]
def baseStart_7984035 : Nat := 118140960795 + 7984035 * 2 ^ 59
def prefixEnd_7984035 : Nat := 4983230072969 + 3 ^ 40 * 7984035 * 2
def baseEnd_7984035 : Nat := 1366549172439925053348199

theorem tailTrace_7984035 : CollatzResearch.WordTrace tailWord_7984035 prefixEnd_7984035 1366549172439925053348199 := by
  unfold tailWord_7984035
  simp only [CollatzResearch.WordTrace]
  refine ⟨291201679630212234464185559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194134453086808156309457039 291201679630212234464185559)
  ·
    refine ⟨436802519445318351696278339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291201679630212234464185559 436802519445318351696278339)
    ·
      refine ⟨655203779167977527544417509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436802519445318351696278339 655203779167977527544417509)
      ·
        refine ⟨122850708593995786414578283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655203779167977527544417509 122850708593995786414578283)
        ·
          refine ⟨184276062890993679621867425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122850708593995786414578283 184276062890993679621867425)
          ·
            refine ⟨138207047168245259716400569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184276062890993679621867425 138207047168245259716400569)
            ·
              refine ⟨103655285376183944787300427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138207047168245259716400569 103655285376183944787300427)
              ·
                refine ⟨155482928064275917180950641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103655285376183944787300427 155482928064275917180950641)
                ·
                  refine ⟨116612196048206937885712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155482928064275917180950641 116612196048206937885712981)
                  ·
                    refine ⟨1366549172439925053348199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116612196048206937885712981 1366549172439925053348199)
                    ·
                      rfl

theorem cell23_7984035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_7984035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984035 prefixEnd_7984035 := by exact prefixLift 7984035
  have htrace : WordTrace (prefixWord ++ tailWord_7984035) baseStart_7984035 baseEnd_7984035 := by
    simpa [prefixWord, tailWord_7984035, baseEnd_7984035] using wordTrace_append hprefix tailTrace_7984035
  have hstable : (prefixWord ++ tailWord_7984035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984035).length < 2 ^ (prefixWord ++ tailWord_7984035).sum := by decide
  have hdescent : baseEnd_7984035 < baseStart_7984035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984054 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7984054 : Nat := 118140960795 + 7984054 * 2 ^ 59
def prefixEnd_7984054 : Nat := 4983230072969 + 3 ^ 40 * 7984054 * 2
def baseEnd_7984054 : Nat := 4099657273452210585707011

theorem tailTrace_7984054 : CollatzResearch.WordTrace tailWord_7984054 prefixEnd_7984054 4099657273452210585707011 := by
  unfold tailWord_7984054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200148288571462544320451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194134915078095600472751477 18200148288571462544320451)
  ·
    refine ⟨27300222432857193816480677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200148288571462544320451 27300222432857193816480677)
    ·
      refine ⟨5118791706160723840590127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27300222432857193816480677 5118791706160723840590127)
      ·
        refine ⟨7678187559241085760885191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118791706160723840590127 7678187559241085760885191)
        ·
          refine ⟨11517281338861628641327787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678187559241085760885191 11517281338861628641327787)
          ·
            refine ⟨17275922008292442961991681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517281338861628641327787 17275922008292442961991681)
            ·
              refine ⟨12956941506219332221493761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17275922008292442961991681 12956941506219332221493761)
              ·
                refine ⟨9717706129664499166120321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12956941506219332221493761 9717706129664499166120321)
                ·
                  refine ⟨7288279597248374374590241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717706129664499166120321 7288279597248374374590241)
                  ·
                    refine ⟨5466209697936280780942681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7288279597248374374590241 5466209697936280780942681)
                    ·
                      refine ⟨4099657273452210585707011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466209697936280780942681 4099657273452210585707011)
                      ·
                        rfl

theorem cell23_7984054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7984054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984054 prefixEnd_7984054 := by exact prefixLift 7984054
  have htrace : WordTrace (prefixWord ++ tailWord_7984054) baseStart_7984054 baseEnd_7984054 := by
    simpa [prefixWord, tailWord_7984054, baseEnd_7984054] using wordTrace_append hprefix tailTrace_7984054
  have hstable : (prefixWord ++ tailWord_7984054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984054).length < 2 ^ (prefixWord ++ tailWord_7984054).sum := by decide
  have hdescent : baseEnd_7984054 < baseStart_7984054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984062 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7984062 : Nat := 118140960795 + 7984062 * 2 ^ 59
def prefixEnd_7984062 : Nat := 4983230072969 + 3 ^ 40 * 7984062 * 2
def baseEnd_7984062 : Nat := 4099661381297446554406973

theorem tailTrace_7984062 : CollatzResearch.WordTrace tailWord_7984062 prefixEnd_7984062 4099661381297446554406973 := by
  unfold tailWord_7984062
  simp only [CollatzResearch.WordTrace]
  refine ⟨36400333050139302259427305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194135109600742945383612293 36400333050139302259427305)
  ·
    refine ⟨27300249787604476694570479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36400333050139302259427305 27300249787604476694570479)
    ·
      refine ⟨40950374681406715041855719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27300249787604476694570479 40950374681406715041855719)
      ·
        refine ⟨61425562022110072562783579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40950374681406715041855719 61425562022110072562783579)
        ·
          refine ⟨92138343033165108844175369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61425562022110072562783579 92138343033165108844175369)
          ·
            refine ⟨69103757274873831633131527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92138343033165108844175369 69103757274873831633131527)
            ·
              refine ⟨103655635912310747449697291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69103757274873831633131527 103655635912310747449697291)
              ·
                refine ⟨155483453868466121174545937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103655635912310747449697291 155483453868466121174545937)
                ·
                  refine ⟨116612590401349590880909453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155483453868466121174545937 116612590401349590880909453)
                  ·
                    refine ⟨43729721400506096580341045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116612590401349590880909453 43729721400506096580341045)
                    ·
                      refine ⟨4099661381297446554406973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43729721400506096580341045 4099661381297446554406973)
                      ·
                        rfl

theorem cell23_7984062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7984062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984062 prefixEnd_7984062 := by exact prefixLift 7984062
  have htrace : WordTrace (prefixWord ++ tailWord_7984062) baseStart_7984062 baseEnd_7984062 := by
    simpa [prefixWord, tailWord_7984062, baseEnd_7984062] using wordTrace_append hprefix tailTrace_7984062
  have hstable : (prefixWord ++ tailWord_7984062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984062).length < 2 ^ (prefixWord ++ tailWord_7984062).sum := by decide
  have hdescent : baseEnd_7984062 < baseStart_7984062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984086 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_7984086 : Nat := 118140960795 + 7984086 * 2 ^ 59
def prefixEnd_7984086 : Nat := 4983230072969 + 3 ^ 40 * 7984086 * 2
def baseEnd_7984086 : Nat := 1366557901611051486835621

theorem tailTrace_7984086 : CollatzResearch.WordTrace tailWord_7984086 prefixEnd_7984086 1366557901611051486835621 := by
  unfold tailWord_7984086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200221234564216885893257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194135693168684980116194741 18200221234564216885893257)
  ·
    refine ⟨13650165925923162664419943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18200221234564216885893257 13650165925923162664419943)
    ·
      refine ⟨20475248888884743996629915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650165925923162664419943 20475248888884743996629915)
      ·
        refine ⟨30712873333327115994944873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20475248888884743996629915 30712873333327115994944873)
        ·
          refine ⟨23034654999995336996208655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30712873333327115994944873 23034654999995336996208655)
          ·
            refine ⟨34551982499993005494312983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23034654999995336996208655 34551982499993005494312983)
            ·
              refine ⟨51827973749989508241469475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34551982499993005494312983 51827973749989508241469475)
              ·
                refine ⟨77741960624984262362204213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51827973749989508241469475 77741960624984262362204213)
                ·
                  refine ⟨7288308808592274596456645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77741960624984262362204213 7288308808592274596456645)
                  ·
                    refine ⟨1366557901611051486835621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288308808592274596456645 1366557901611051486835621)
                    ·
                      rfl

theorem cell23_7984086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_7984086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984086 prefixEnd_7984086 := by exact prefixLift 7984086
  have htrace : WordTrace (prefixWord ++ tailWord_7984086) baseStart_7984086 baseEnd_7984086 := by
    simpa [prefixWord, tailWord_7984086, baseEnd_7984086] using wordTrace_append hprefix tailTrace_7984086
  have hstable : (prefixWord ++ tailWord_7984086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984086).length < 2 ^ (prefixWord ++ tailWord_7984086).sum := by decide
  have hdescent : baseEnd_7984086 < baseStart_7984086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984103 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 1, 4]
def baseStart_7984103 : Nat := 118140960795 + 7984103 * 2 ^ 59
def prefixEnd_7984103 : Nat := 4983230072969 + 3 ^ 40 * 7984103 * 2
def baseEnd_7984103 : Nat := 1366560811334760297998095

theorem tailTrace_7984103 : CollatzResearch.WordTrace tailWord_7984103 prefixEnd_7984103 1366560811334760297998095 := by
  unfold tailWord_7984103
  simp only [CollatzResearch.WordTrace]
  refine ⟨291204159793965882077660963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194136106529310588051773975 291204159793965882077660963)
  ·
    refine ⟨436806239690948823116491445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291204159793965882077660963 436806239690948823116491445)
    ·
      refine ⟨40950584971026452167171073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436806239690948823116491445 40950584971026452167171073)
      ·
        refine ⟨30712938728269839125378305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40950584971026452167171073 30712938728269839125378305)
        ·
          refine ⟨23034704046202379344033729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30712938728269839125378305 23034704046202379344033729)
          ·
            refine ⟨17276028034651784508025297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23034704046202379344033729 17276028034651784508025297)
            ·
              refine ⟨12957021025988838381018973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276028034651784508025297 12957021025988838381018973)
              ·
                refine ⟨4858882884745814392882115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12957021025988838381018973 4858882884745814392882115)
                ·
                  refine ⟨7288324327118721589323173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858882884745814392882115 7288324327118721589323173)
                  ·
                    refine ⟨1366560811334760297998095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288324327118721589323173 1366560811334760297998095)
                    ·
                      rfl

theorem cell23_7984103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_7984103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984103 prefixEnd_7984103 := by exact prefixLift 7984103
  have htrace : WordTrace (prefixWord ++ tailWord_7984103) baseStart_7984103 baseEnd_7984103 := by
    simpa [prefixWord, tailWord_7984103, baseEnd_7984103] using wordTrace_append hprefix tailTrace_7984103
  have hstable : (prefixWord ++ tailWord_7984103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984103).length < 2 ^ (prefixWord ++ tailWord_7984103).sum := by decide
  have hdescent : baseEnd_7984103 < baseStart_7984103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984159 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 4, 4]
def baseStart_7984159 : Nat := 118140960795 + 7984159 * 2 ^ 59
def prefixEnd_7984159 : Nat := 4983230072969 + 3 ^ 40 * 7984159 * 2
def baseEnd_7984159 : Nat := 1366570396306977558298009

theorem tailTrace_7984159 : CollatzResearch.WordTrace tailWord_7984159 prefixEnd_7984159 1366570396306977558298009 := by
  unfold tailWord_7984159
  simp only [CollatzResearch.WordTrace]
  refine ⟨291206202281763003641699531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194137468187842002427799687 291206202281763003641699531)
  ·
    refine ⟨436809303422644505462549297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291206202281763003641699531 436809303422644505462549297)
    ·
      refine ⟨327606977566983379096911973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436809303422644505462549297 327606977566983379096911973)
      ·
        refine ⟨61426308293809383580670995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327606977566983379096911973 61426308293809383580670995)
        ·
          refine ⟨92139462440714075371006493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61426308293809383580670995 92139462440714075371006493)
          ·
            refine ⟨34552298415267778264127435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92139462440714075371006493 34552298415267778264127435)
            ·
              refine ⟨51828447622901667396191153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34552298415267778264127435 51828447622901667396191153)
              ·
                refine ⟨38871335717176250547143365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51828447622901667396191153 38871335717176250547143365)
                ·
                  refine ⟨7288375446970546977589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38871335717176250547143365 7288375446970546977589381)
                  ·
                    refine ⟨1366570396306977558298009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288375446970546977589381 1366570396306977558298009)
                    ·
                      rfl

theorem cell23_7984159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_7984159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984159 prefixEnd_7984159 := by exact prefixLift 7984159
  have htrace : WordTrace (prefixWord ++ tailWord_7984159) baseStart_7984159 baseEnd_7984159 := by
    simpa [prefixWord, tailWord_7984159, baseEnd_7984159] using wordTrace_append hprefix tailTrace_7984159
  have hstable : (prefixWord ++ tailWord_7984159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984159).length < 2 ^ (prefixWord ++ tailWord_7984159).sum := by decide
  have hdescent : baseEnd_7984159 < baseStart_7984159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984189 : List Nat := [1, 4, 1, 3, 1, 3, 2, 8]
def baseStart_7984189 : Nat := 118140960795 + 7984189 * 2 ^ 59
def prefixEnd_7984189 : Nat := 4983230072969 + 3 ^ 40 * 7984189 * 2
def baseEnd_7984189 : Nat := 151841725679280279908107

theorem tailTrace_7984189 : CollatzResearch.WordTrace tailWord_7984189 prefixEnd_7984189 151841725679280279908107 := by
  unfold tailWord_7984189
  simp only [CollatzResearch.WordTrace]
  refine ⟨291207296471654318765291621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194138197647769545843527747 291207296471654318765291621)
  ·
    refine ⟨54601368088435184768492179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291207296471654318765291621 54601368088435184768492179)
    ·
      refine ⟨81902052132652777152738269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54601368088435184768492179 81902052132652777152738269)
      ·
        refine ⟨30713269549744791432276851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81902052132652777152738269 30713269549744791432276851)
        ·
          refine ⟨46069904324617187148415277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30713269549744791432276851 46069904324617187148415277)
          ·
            refine ⟨17276214121731445180655729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46069904324617187148415277 17276214121731445180655729)
            ·
              refine ⟨12957160591298583885491797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276214121731445180655729 12957160591298583885491797)
              ·
                refine ⟨151841725679280279908107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12957160591298583885491797 151841725679280279908107)
                ·
                  rfl

theorem cell23_7984189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 8].length) (baseStart_7984189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984189 prefixEnd_7984189 := by exact prefixLift 7984189
  have htrace : WordTrace (prefixWord ++ tailWord_7984189) baseStart_7984189 baseEnd_7984189 := by
    simpa [prefixWord, tailWord_7984189, baseEnd_7984189] using wordTrace_append hprefix tailTrace_7984189
  have hstable : (prefixWord ++ tailWord_7984189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984189).length < 2 ^ (prefixWord ++ tailWord_7984189).sum := by decide
  have hdescent : baseEnd_7984189 < baseStart_7984189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984192 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_7984192 : Nat := 118140960795 + 7984192 * 2 ^ 59
def prefixEnd_7984192 : Nat := 4983230072969 + 3 ^ 40 * 7984192 * 2
def baseEnd_7984192 : Nat := 4099728133782531045781375

theorem tailTrace_7984192 : CollatzResearch.WordTrace tailWord_7984192 prefixEnd_7984192 4099728133782531045781375 := by
  unfold tailWord_7984192
  simp only [CollatzResearch.WordTrace]
  refine ⟨145603702945321725138825415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194138270593762300185100553 145603702945321725138825415)
  ·
    refine ⟨218405554417982587708238123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145603702945321725138825415 218405554417982587708238123)
    ·
      refine ⟨327608331626973881562357185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218405554417982587708238123 327608331626973881562357185)
      ·
        refine ⟨245706248720230411171767889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327608331626973881562357185 245706248720230411171767889)
        ·
          refine ⟨184279686540172808378825917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245706248720230411171767889 184279686540172808378825917)
          ·
            refine ⟨69104882452564803142059719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184279686540172808378825917 69104882452564803142059719)
            ·
              refine ⟨103657323678847204713089579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69104882452564803142059719 103657323678847204713089579)
              ·
                refine ⟨155485985518270807069634369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103657323678847204713089579 155485985518270807069634369)
                ·
                  refine ⟨116614489138703105302225777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155485985518270807069634369 116614489138703105302225777)
                  ·
                    refine ⟨87460866854027328976669333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116614489138703105302225777 87460866854027328976669333)
                    ·
                      refine ⟨4099728133782531045781375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87460866854027328976669333 4099728133782531045781375)
                      ·
                        rfl

theorem cell23_7984192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_7984192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984192 prefixEnd_7984192 := by exact prefixLift 7984192
  have htrace : WordTrace (prefixWord ++ tailWord_7984192) baseStart_7984192 baseEnd_7984192 := by
    simpa [prefixWord, tailWord_7984192, baseEnd_7984192] using wordTrace_append hprefix tailTrace_7984192
  have hstable : (prefixWord ++ tailWord_7984192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984192).length < 2 ^ (prefixWord ++ tailWord_7984192).sum := by decide
  have hdescent : baseEnd_7984192 < baseStart_7984192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984193 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7984193 : Nat := 118140960795 + 7984193 * 2 ^ 59
def prefixEnd_7984193 : Nat := 4983230072969 + 3 ^ 40 * 7984193 * 2
def baseEnd_7984193 : Nat := 1366576215754395180622957

theorem tailTrace_7984193 : CollatzResearch.WordTrace tailWord_7984193 prefixEnd_7984193 1366576215754395180622957 := by
  unfold tailWord_7984193
  simp only [CollatzResearch.WordTrace]
  refine ⟨291207442363639827448437233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194138294909093218298958155 291207442363639827448437233)
  ·
    refine ⟨218405581772729870586327925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291207442363639827448437233 218405581772729870586327925)
    ·
      refine ⟨20475523291193425367468243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218405581772729870586327925 20475523291193425367468243)
      ·
        refine ⟨30713284936790138051202365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20475523291193425367468243 30713284936790138051202365)
        ·
          refine ⟨11517481851296301769200887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30713284936790138051202365 11517481851296301769200887)
          ·
            refine ⟨17276222776944452653801331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517481851296301769200887 17276222776944452653801331)
            ·
              refine ⟨25914334165416678980701997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17276222776944452653801331 25914334165416678980701997)
              ·
                refine ⟨9717875312031254617763249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25914334165416678980701997 9717875312031254617763249)
                ·
                  refine ⟨7288406484023440963322437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717875312031254617763249 7288406484023440963322437)
                  ·
                    refine ⟨1366576215754395180622957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7288406484023440963322437 1366576215754395180622957)
                    ·
                      rfl

theorem cell23_7984193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7984193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984193 prefixEnd_7984193 := by exact prefixLift 7984193
  have htrace : WordTrace (prefixWord ++ tailWord_7984193) baseStart_7984193 baseEnd_7984193 := by
    simpa [prefixWord, tailWord_7984193, baseEnd_7984193] using wordTrace_append hprefix tailTrace_7984193
  have hstable : (prefixWord ++ tailWord_7984193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984193).length < 2 ^ (prefixWord ++ tailWord_7984193).sum := by decide
  have hdescent : baseEnd_7984193 < baseStart_7984193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984233 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_7984233 : Nat := 118140960795 + 7984233 * 2 ^ 59
def prefixEnd_7984233 : Nat := 4983230072969 + 3 ^ 40 * 7984233 * 2
def baseEnd_7984233 : Nat := 4099749186489365385368687

theorem tailTrace_7984233 : CollatzResearch.WordTrace tailWord_7984233 prefixEnd_7984233 4099749186489365385368687 := by
  unfold tailWord_7984233
  simp only [CollatzResearch.WordTrace]
  refine ⟨291208901283494914279893353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194139267522329942853262235 291208901283494914279893353)
  ·
    refine ⟨218406675962621185709920015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291208901283494914279893353 218406675962621185709920015)
    ·
      refine ⟨327610013943931778564880023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218406675962621185709920015 327610013943931778564880023)
      ·
        refine ⟨491415020915897667847320035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327610013943931778564880023 491415020915897667847320035)
        ·
          refine ⟨737122531373846501770980053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491415020915897667847320035 737122531373846501770980053)
          ·
            refine ⟨17276309329074527385257345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 737122531373846501770980053 17276309329074527385257345)
            ·
              refine ⟨12957231996805895538943009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276309329074527385257345 12957231996805895538943009)
              ·
                refine ⟨9717923997604421654207257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12957231996805895538943009 9717923997604421654207257)
                ·
                  refine ⟨7288442998203316240655443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717923997604421654207257 7288442998203316240655443)
                  ·
                    refine ⟨10932664497304974360983165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288442998203316240655443 10932664497304974360983165)
                    ·
                      refine ⟨4099749186489365385368687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932664497304974360983165 4099749186489365385368687)
                      ·
                        rfl

theorem cell23_7984233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_7984233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984233 prefixEnd_7984233 := by exact prefixLift 7984233
  have htrace : WordTrace (prefixWord ++ tailWord_7984233) baseStart_7984233 baseEnd_7984233 := by
    simpa [prefixWord, tailWord_7984233, baseEnd_7984233] using wordTrace_append hprefix tailTrace_7984233
  have hstable : (prefixWord ++ tailWord_7984233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984233).length < 2 ^ (prefixWord ++ tailWord_7984233).sum := by decide
  have hdescent : baseEnd_7984233 < baseStart_7984233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984234 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7984234 : Nat := 118140960795 + 7984234 * 2 ^ 59
def prefixEnd_7984234 : Nat := 4983230072969 + 3 ^ 40 * 7984234 * 2
def baseEnd_7984234 : Nat := 4099749699970019881456183

theorem tailTrace_7984234 : CollatzResearch.WordTrace tailWord_7984234 prefixEnd_7984234 4099749699970019881456183 := by
  unfold tailWord_7984234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72802234439122822862669939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194139291837660860967119837 72802234439122822862669939)
  ·
    refine ⟨109203351658684234294004909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72802234439122822862669939 109203351658684234294004909)
    ·
      refine ⟨40951256872006587860251841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109203351658684234294004909 40951256872006587860251841)
      ·
        refine ⟨30713442654004940895188881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40951256872006587860251841 30713442654004940895188881)
        ·
          refine ⟨23035081990503705671391661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30713442654004940895188881 23035081990503705671391661)
          ·
            refine ⟨8638155746438889626771873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23035081990503705671391661 8638155746438889626771873)
            ·
              refine ⟨6478616809829167220078905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638155746438889626771873 6478616809829167220078905)
              ·
                refine ⟨4858962607371875415059179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478616809829167220078905 4858962607371875415059179)
                ·
                  refine ⟨7288443911057813122588769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858962607371875415059179 7288443911057813122588769)
                  ·
                    refine ⟨5466332933293359841941577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7288443911057813122588769 5466332933293359841941577)
                    ·
                      refine ⟨4099749699970019881456183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466332933293359841941577 4099749699970019881456183)
                      ·
                        rfl

theorem cell23_7984234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7984234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984234 prefixEnd_7984234 := by exact prefixLift 7984234
  have htrace : WordTrace (prefixWord ++ tailWord_7984234) baseStart_7984234 baseEnd_7984234 := by
    simpa [prefixWord, tailWord_7984234, baseEnd_7984234] using wordTrace_append hprefix tailTrace_7984234
  have hstable : (prefixWord ++ tailWord_7984234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984234).length < 2 ^ (prefixWord ++ tailWord_7984234).sum := by decide
  have hdescent : baseEnd_7984234 < baseStart_7984234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984256 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2]
def baseStart_7984256 : Nat := 118140960795 + 7984256 * 2 ^ 59
def prefixEnd_7984256 : Nat := 4983230072969 + 3 ^ 40 * 7984256 * 2
def baseEnd_7984256 : Nat := 4099760996544418795381081

theorem tailTrace_7984256 : CollatzResearch.WordTrace tailWord_7984256 prefixEnd_7984256 4099760996544418795381081 := by
  unfold tailWord_7984256
  simp only [CollatzResearch.WordTrace]
  refine ⟨145604870081205794603990311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194139826774941059471987081 145604870081205794603990311)
  ·
    refine ⟨218407305121808691905985467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145604870081205794603990311 218407305121808691905985467)
    ·
      refine ⟨327610957682713037858978201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218407305121808691905985467 327610957682713037858978201)
      ·
        refine ⟨245708218262034778394233651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327610957682713037858978201 245708218262034778394233651)
        ·
          refine ⟨368562327393052167591350477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245708218262034778394233651 368562327393052167591350477)
          ·
            refine ⟨138210872772394562846756429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368562327393052167591350477 138210872772394562846756429)
            ·
              refine ⟨51829077289647961067533661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138210872772394562846756429 51829077289647961067533661)
              ·
                refine ⟨19435903983617985400325123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51829077289647961067533661 19435903983617985400325123)
                ·
                  refine ⟨29153855975426978100487685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19435903983617985400325123 29153855975426978100487685)
                  ·
                    refine ⟨5466347995392558393841441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29153855975426978100487685 5466347995392558393841441)
                    ·
                      refine ⟨4099760996544418795381081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466347995392558393841441 4099760996544418795381081)
                      ·
                        rfl

theorem cell23_7984256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_7984256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984256 prefixEnd_7984256 := by exact prefixLift 7984256
  have htrace : WordTrace (prefixWord ++ tailWord_7984256) baseStart_7984256 baseEnd_7984256 := by
    simpa [prefixWord, tailWord_7984256, baseEnd_7984256] using wordTrace_append hprefix tailTrace_7984256
  have hstable : (prefixWord ++ tailWord_7984256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984256).length < 2 ^ (prefixWord ++ tailWord_7984256).sum := by decide
  have hdescent : baseEnd_7984256 < baseStart_7984256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984259 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3]
def baseStart_7984259 : Nat := 118140960795 + 7984259 * 2 ^ 59
def prefixEnd_7984259 : Nat := 4983230072969 + 3 ^ 40 * 7984259 * 2
def baseEnd_7984259 : Nat := 4099762536986382283643567

theorem tailTrace_7984259 : CollatzResearch.WordTrace tailWord_7984259 prefixEnd_7984259 4099762536986382283643567 := by
  unfold tailWord_7984259
  simp only [CollatzResearch.WordTrace]
  refine ⟨291209849581400720720339831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194139899720933813813559887 291209849581400720720339831)
  ·
    refine ⟨436814774372101081080509747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291209849581400720720339831 436814774372101081080509747)
    ·
      refine ⟨655222161558151621620764621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436814774372101081080509747 655222161558151621620764621)
      ·
        refine ⟨245708310584306858107786733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655222161558151621620764621 245708310584306858107786733)
        ·
          refine ⟨92140616469115071790420025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245708310584306858107786733 92140616469115071790420025)
          ·
            refine ⟨69105462351836303842815019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92140616469115071790420025 69105462351836303842815019)
            ·
              refine ⟨103658193527754455764222529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69105462351836303842815019 103658193527754455764222529)
              ·
                refine ⟨77743645145815841823166897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103658193527754455764222529 77743645145815841823166897)
                ·
                  refine ⟨58307733859361881367375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77743645145815841823166897 58307733859361881367375173)
                  ·
                    refine ⟨10932700098630352756382845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58307733859361881367375173 10932700098630352756382845)
                    ·
                      refine ⟨4099762536986382283643567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932700098630352756382845 4099762536986382283643567)
                      ·
                        rfl

theorem cell23_7984259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_7984259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984259 prefixEnd_7984259 := by exact prefixLift 7984259
  have htrace : WordTrace (prefixWord ++ tailWord_7984259) baseStart_7984259 baseEnd_7984259 := by
    simpa [prefixWord, tailWord_7984259, baseEnd_7984259] using wordTrace_append hprefix tailTrace_7984259
  have hstable : (prefixWord ++ tailWord_7984259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984259).length < 2 ^ (prefixWord ++ tailWord_7984259).sum := by decide
  have hdescent : baseEnd_7984259 < baseStart_7984259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984306 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_7984306 : Nat := 118140960795 + 7984306 * 2 ^ 59
def prefixEnd_7984306 : Nat := 4983230072969 + 3 ^ 40 * 7984306 * 2
def baseEnd_7984306 : Nat := 4099786670577143599755851

theorem tailTrace_7984306 : CollatzResearch.WordTrace tailWord_7984306 prefixEnd_7984306 4099786670577143599755851 := by
  unfold tailWord_7984306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72802890953057611936825193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194141042541486965164867181 72802890953057611936825193)
  ·
    refine ⟨54602168214793208952618895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72802890953057611936825193 54602168214793208952618895)
    ·
      refine ⟨81903252322189813428928343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54602168214793208952618895 81903252322189813428928343)
      ·
        refine ⟨122854878483284720143392515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81903252322189813428928343 122854878483284720143392515)
        ·
          refine ⟨184282317724927080215088773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122854878483284720143392515 184282317724927080215088773)
          ·
            refine ⟨34552934573423827540329145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184282317724927080215088773 34552934573423827540329145)
            ·
              refine ⟨25914700930067870655246859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34552934573423827540329145 25914700930067870655246859)
              ·
                refine ⟨38872051395101805982870289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25914700930067870655246859 38872051395101805982870289)
                ·
                  refine ⟨29154038546326354487152717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38872051395101805982870289 29154038546326354487152717)
                  ·
                    refine ⟨10932764454872382932682269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29154038546326354487152717 10932764454872382932682269)
                    ·
                      refine ⟨4099786670577143599755851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932764454872382932682269 4099786670577143599755851)
                      ·
                        rfl

theorem cell23_7984306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_7984306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984306 prefixEnd_7984306 := by exact prefixLift 7984306
  have htrace : WordTrace (prefixWord ++ tailWord_7984306) baseStart_7984306 baseEnd_7984306 := by
    simpa [prefixWord, tailWord_7984306, baseEnd_7984306] using wordTrace_append hprefix tailTrace_7984306
  have hstable : (prefixWord ++ tailWord_7984306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984306).length < 2 ^ (prefixWord ++ tailWord_7984306).sum := by decide
  have hdescent : baseEnd_7984306 < baseStart_7984306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984366 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_7984366 : Nat := 118140960795 + 7984366 * 2 ^ 59
def prefixEnd_7984366 : Nat := 4983230072969 + 3 ^ 40 * 7984366 * 2
def baseEnd_7984366 : Nat := 4099817479416413365005575

theorem tailTrace_7984366 : CollatzResearch.WordTrace tailWord_7984366 prefixEnd_7984366 4099817479416413365005575 := by
  unfold tailWord_7984366
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401719024001634749310619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194142501461342051996323301 36401719024001634749310619)
  ·
    refine ⟨54602578536002452123965929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36401719024001634749310619 54602578536002452123965929)
    ·
      refine ⟨40951933902001839092974447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54602578536002452123965929 40951933902001839092974447)
      ·
        refine ⟨61427900853002758639461671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40951933902001839092974447 61427900853002758639461671)
        ·
          refine ⟨92141851279504137959192507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61427900853002758639461671 92141851279504137959192507)
          ·
            refine ⟨138212776919256206938788761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92141851279504137959192507 138212776919256206938788761)
            ·
              refine ⟨103659582689442155204091571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138212776919256206938788761 103659582689442155204091571)
              ·
                refine ⟨155489374034163232806137357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103659582689442155204091571 155489374034163232806137357)
                ·
                  refine ⟨58308515262811212302301509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155489374034163232806137357 58308515262811212302301509)
                  ·
                    refine ⟨10932846611777102306681533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58308515262811212302301509 10932846611777102306681533)
                    ·
                      refine ⟨4099817479416413365005575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932846611777102306681533 4099817479416413365005575)
                      ·
                        rfl

theorem cell23_7984366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_7984366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984366 prefixEnd_7984366 := by exact prefixLift 7984366
  have htrace : WordTrace (prefixWord ++ tailWord_7984366) baseStart_7984366 baseEnd_7984366 := by
    simpa [prefixWord, tailWord_7984366, baseEnd_7984366] using wordTrace_append hprefix tailTrace_7984366
  have hstable : (prefixWord ++ tailWord_7984366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984366).length < 2 ^ (prefixWord ++ tailWord_7984366).sum := by decide
  have hdescent : baseEnd_7984366 < baseStart_7984366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984383 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_7984383 : Nat := 118140960795 + 7984383 * 2 ^ 59
def prefixEnd_7984383 : Nat := 4983230072969 + 3 ^ 40 * 7984383 * 2
def baseEnd_7984383 : Nat := 4099826208587539798492997

theorem tailTrace_7984383 : CollatzResearch.WordTrace tailWord_7984383 prefixEnd_7984383 4099826208587539798492997 := by
  unfold tailWord_7984383
  simp only [CollatzResearch.WordTrace]
  refine ⟨291214372232951489897853803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194142914821967659931902535 291214372232951489897853803)
  ·
    refine ⟨436821558349427234846780705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291214372232951489897853803 436821558349427234846780705)
    ·
      refine ⟨327616168762070426135085529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436821558349427234846780705 327616168762070426135085529)
      ·
        refine ⟨245712126571552819601314147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327616168762070426135085529 245712126571552819601314147)
        ·
          refine ⟨368568189857329229401971221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245712126571552819601314147 368568189857329229401971221)
          ·
            refine ⟨17276633899562307628217401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368568189857329229401971221 17276633899562307628217401)
            ·
              refine ⟨12957475424671730721163051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276633899562307628217401 12957475424671730721163051)
              ·
                refine ⟨19436213137007596081744577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12957475424671730721163051 19436213137007596081744577)
                ·
                  refine ⟨14577159852755697061308433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19436213137007596081744577 14577159852755697061308433)
                  ·
                    refine ⟨10932869889566772795981325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14577159852755697061308433 10932869889566772795981325)
                    ·
                      refine ⟨4099826208587539798492997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932869889566772795981325 4099826208587539798492997)
                      ·
                        rfl

theorem cell23_7984383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_7984383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984383 prefixEnd_7984383 := by exact prefixLift 7984383
  have htrace : WordTrace (prefixWord ++ tailWord_7984383) baseStart_7984383 baseEnd_7984383 := by
    simpa [prefixWord, tailWord_7984383, baseEnd_7984383] using wordTrace_append hprefix tailTrace_7984383
  have hstable : (prefixWord ++ tailWord_7984383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984383).length < 2 ^ (prefixWord ++ tailWord_7984383).sum := by decide
  have hdescent : baseEnd_7984383 < baseStart_7984383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984409 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_7984409 : Nat := 118140960795 + 7984409 * 2 ^ 59
def prefixEnd_7984409 : Nat := 4983230072969 + 3 ^ 40 * 7984409 * 2
def baseEnd_7984409 : Nat := 4099839559084556696767877

theorem tailTrace_7984409 : CollatzResearch.WordTrace tailWord_7984409 prefixEnd_7984409 4099839559084556696767877 := by
  unfold tailWord_7984409
  simp only [CollatzResearch.WordTrace]
  refine ⟨291215320530857296338300281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194143547020571530892200187 291215320530857296338300281)
  ·
    refine ⟨218411490398142972253725211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291215320530857296338300281 218411490398142972253725211)
    ·
      refine ⟨327617235597214458380587817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218411490398142972253725211 327617235597214458380587817)
      ·
        refine ⟨245712926697910843785440863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327617235597214458380587817 245712926697910843785440863)
        ·
          refine ⟨368569390046866265678161295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245712926697910843785440863 368569390046866265678161295)
          ·
            refine ⟨552854085070299398517241943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368569390046866265678161295 552854085070299398517241943)
            ·
              refine ⟨829281127605449097775862915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552854085070299398517241943 829281127605449097775862915)
              ·
                refine ⟨1243921691408173646663794373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829281127605449097775862915 1243921691408173646663794373)
                ·
                  refine ⟨233235317139032558749461445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243921691408173646663794373 233235317139032558749461445)
                  ·
                    refine ⟨43731621963568604765524021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233235317139032558749461445 43731621963568604765524021)
                    ·
                      refine ⟨4099839559084556696767877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43731621963568604765524021 4099839559084556696767877)
                      ·
                        rfl

theorem cell23_7984409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_7984409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984409 prefixEnd_7984409 := by exact prefixLift 7984409
  have htrace : WordTrace (prefixWord ++ tailWord_7984409) baseStart_7984409 baseEnd_7984409 := by
    simpa [prefixWord, tailWord_7984409, baseEnd_7984409] using wordTrace_append hprefix tailTrace_7984409
  have hstable : (prefixWord ++ tailWord_7984409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984409).length < 2 ^ (prefixWord ++ tailWord_7984409).sum := by decide
  have hdescent : baseEnd_7984409 < baseStart_7984409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984447 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 1, 1, 3]
def baseStart_7984447 : Nat := 118140960795 + 7984447 * 2 ^ 59
def prefixEnd_7984447 : Nat := 4983230072969 + 3 ^ 40 * 7984447 * 2
def baseEnd_7984447 : Nat := 4099859071349427548092703

theorem tailTrace_7984447 : CollatzResearch.WordTrace tailWord_7984447 prefixEnd_7984447 4099859071349427548092703 := by
  unfold tailWord_7984447
  simp only [CollatzResearch.WordTrace]
  refine ⟨291216706504719628828183595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194144471003146419218789063 291216706504719628828183595)
  ·
    refine ⟨436825059757079443242275393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291216706504719628828183595 436825059757079443242275393)
    ·
      refine ⟨327618794817809582431706545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436825059757079443242275393 327618794817809582431706545)
      ·
        refine ⟨245714096113357186823779909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327618794817809582431706545 245714096113357186823779909)
        ·
          refine ⟨46071393021254472529458733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245714096113357186823779909 46071393021254472529458733)
          ·
            refine ⟨17276772382970427198547025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46071393021254472529458733 17276772382970427198547025)
            ·
              refine ⟨12957579287227820398910269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17276772382970427198547025 12957579287227820398910269)
              ·
                refine ⟨4859092232710432649591351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12957579287227820398910269 4859092232710432649591351)
                ·
                  refine ⟨7288638349065648974387027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859092232710432649591351 7288638349065648974387027)
                  ·
                    refine ⟨10932957523598473461580541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288638349065648974387027 10932957523598473461580541)
                    ·
                      refine ⟨4099859071349427548092703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10932957523598473461580541 4099859071349427548092703)
                      ·
                        rfl

theorem cell23_7984447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_7984447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984447 prefixEnd_7984447 := by exact prefixLift 7984447
  have htrace : WordTrace (prefixWord ++ tailWord_7984447) baseStart_7984447 baseEnd_7984447 := by
    simpa [prefixWord, tailWord_7984447, baseEnd_7984447] using wordTrace_append hprefix tailTrace_7984447
  have hstable : (prefixWord ++ tailWord_7984447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984447).length < 2 ^ (prefixWord ++ tailWord_7984447).sum := by decide
  have hdescent : baseEnd_7984447 < baseStart_7984447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984454 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7984454 : Nat := 118140960795 + 7984454 * 2 ^ 59
def prefixEnd_7984454 : Nat := 4983230072969 + 3 ^ 40 * 7984454 * 2
def baseEnd_7984454 : Nat := 455540296190445446745019

theorem tailTrace_7984454 : CollatzResearch.WordTrace tailWord_7984454 prefixEnd_7984454 455540296190445446745019 := by
  unfold tailWord_7984454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100530056740445906990263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194144641210462846015792277 9100530056740445906990263)
  ·
    refine ⟨13650795085110668860485395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100530056740445906990263 13650795085110668860485395)
    ·
      refine ⟨20476192627666003290728093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650795085110668860485395 20476192627666003290728093)
      ·
        refine ⟨7678572235374751234023035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20476192627666003290728093 7678572235374751234023035)
        ·
          refine ⟨11517858353062126851034553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678572235374751234023035 11517858353062126851034553)
          ·
            refine ⟨8638393764796595138275915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11517858353062126851034553 8638393764796595138275915)
            ·
              refine ⟨12957590647194892707413873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8638393764796595138275915 12957590647194892707413873)
              ·
                refine ⟨9718192985396169530560405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12957590647194892707413873 9718192985396169530560405)
                ·
                  refine ⟨455540296190445446745019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9718192985396169530560405 455540296190445446745019)
                  ·
                    rfl

theorem cell23_7984454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7984454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984454 prefixEnd_7984454 := by exact prefixLift 7984454
  have htrace : WordTrace (prefixWord ++ tailWord_7984454) baseStart_7984454 baseEnd_7984454 := by
    simpa [prefixWord, tailWord_7984454, baseEnd_7984454] using wordTrace_append hprefix tailTrace_7984454
  have hstable : (prefixWord ++ tailWord_7984454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984454).length < 2 ^ (prefixWord ++ tailWord_7984454).sum := by decide
  have hdescent : baseEnd_7984454 < baseStart_7984454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984456 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_7984456 : Nat := 118140960795 + 7984456 * 2 ^ 59
def prefixEnd_7984456 : Nat := 4983230072969 + 3 ^ 40 * 7984456 * 2
def baseEnd_7984456 : Nat := 4099863692675318012880161

theorem tailTrace_7984456 : CollatzResearch.WordTrace tailWord_7984456 prefixEnd_7984456 4099863692675318012880161 := by
  unfold tailWord_7984456
  simp only [CollatzResearch.WordTrace]
  refine ⟨145608517380843511682630611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194144689841124682243507481 145608517380843511682630611)
  ·
    refine ⟨218412776071265267523945917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145608517380843511682630611 218412776071265267523945917)
    ·
      refine ⟨81904791026724475321479719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218412776071265267523945917 81904791026724475321479719)
      ·
        refine ⟨122857186540086712982219579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81904791026724475321479719 122857186540086712982219579)
        ·
          refine ⟨184285779810130069473329369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122857186540086712982219579 184285779810130069473329369)
          ·
            refine ⟨138214334857597552104997027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184285779810130069473329369 138214334857597552104997027)
            ·
              refine ⟨207321502286396328157495541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138214334857597552104997027 207321502286396328157495541)
              ·
                refine ⟨19436390839349655764765207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207321502286396328157495541 19436390839349655764765207)
                ·
                  refine ⟨29154586259024483647147811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19436390839349655764765207 29154586259024483647147811)
                  ·
                    refine ⟨43731879388536725470721717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29154586259024483647147811 43731879388536725470721717)
                    ·
                      refine ⟨4099863692675318012880161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43731879388536725470721717 4099863692675318012880161)
                      ·
                        rfl

theorem cell23_7984456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_7984456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984456 prefixEnd_7984456 := by exact prefixLift 7984456
  have htrace : WordTrace (prefixWord ++ tailWord_7984456) baseStart_7984456 baseEnd_7984456 := by
    simpa [prefixWord, tailWord_7984456, baseEnd_7984456] using wordTrace_append hprefix tailTrace_7984456
  have hstable : (prefixWord ++ tailWord_7984456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984456).length < 2 ^ (prefixWord ++ tailWord_7984456).sum := by decide
  have hdescent : baseEnd_7984456 < baseStart_7984456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984466 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_7984466 : Nat := 118140960795 + 7984466 * 2 ^ 59
def prefixEnd_7984466 : Nat := 4983230072969 + 3 ^ 40 * 7984466 * 2
def baseEnd_7984466 : Nat := 4099868827481862973755115

theorem tailTrace_7984466 : CollatzResearch.WordTrace tailWord_7984466 prefixEnd_7984466 4099868827481862973755115 := by
  unfold tailWord_7984466
  simp only [CollatzResearch.WordTrace]
  refine ⟨72804349872912698768281313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194144932994433863382083501 72804349872912698768281313)
  ·
    refine ⟨54603262404684524076210985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72804349872912698768281313 54603262404684524076210985)
    ·
      refine ⟨40952446803513393057158239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54603262404684524076210985 40952446803513393057158239)
      ·
        refine ⟨61428670205270089585737359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40952446803513393057158239 61428670205270089585737359)
        ·
          refine ⟨92143005307905134378606039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61428670205270089585737359 92143005307905134378606039)
          ·
            refine ⟨138214507961857701567909059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92143005307905134378606039 138214507961857701567909059)
            ·
              refine ⟨207321761942786552351863589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138214507961857701567909059 207321761942786552351863589)
              ·
                refine ⟨38872830364272478565974423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207321761942786552351863589 38872830364272478565974423)
                ·
                  refine ⟨58309245546408717848961635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38872830364272478565974423 58309245546408717848961635)
                  ·
                    refine ⟨87463868319613076773442453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58309245546408717848961635 87463868319613076773442453)
                    ·
                      refine ⟨4099868827481862973755115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87463868319613076773442453 4099868827481862973755115)
                      ·
                        rfl

theorem cell23_7984466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_7984466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984466 prefixEnd_7984466 := by exact prefixLift 7984466
  have htrace : WordTrace (prefixWord ++ tailWord_7984466) baseStart_7984466 baseEnd_7984466 := by
    simpa [prefixWord, tailWord_7984466, baseEnd_7984466] using wordTrace_append hprefix tailTrace_7984466
  have hstable : (prefixWord ++ tailWord_7984466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984466).length < 2 ^ (prefixWord ++ tailWord_7984466).sum := by decide
  have hdescent : baseEnd_7984466 < baseStart_7984466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984483 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7984483 : Nat := 118140960795 + 7984483 * 2 ^ 59
def prefixEnd_7984483 : Nat := 4983230072969 + 3 ^ 40 * 7984483 * 2
def baseEnd_7984483 : Nat := 4099877556652989407242537

theorem tailTrace_7984483 : CollatzResearch.WordTrace tailWord_7984483 prefixEnd_7984483 4099877556652989407242537 := by
  unfold tailWord_7984483
  simp only [CollatzResearch.WordTrace]
  refine ⟨291218019532589206976494103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194145346355059471317662735 291218019532589206976494103)
  ·
    refine ⟨436827029298883810464741155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291218019532589206976494103 436827029298883810464741155)
    ·
      refine ⟨655240543948325715697111733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436827029298883810464741155 655240543948325715697111733)
      ·
        refine ⟨61428800995155535846604225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 655240543948325715697111733 61428800995155535846604225)
        ·
          refine ⟨46071600746366651884953169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61428800995155535846604225 46071600746366651884953169)
          ·
            refine ⟨34553700559774988913714877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46071600746366651884953169 34553700559774988913714877)
            ·
              refine ⟨12957637709915620842643079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34553700559774988913714877 12957637709915620842643079)
              ·
                refine ⟨19436456564873431263964619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12957637709915620842643079 19436456564873431263964619)
                ·
                  refine ⟨29154684847310146895946929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19436456564873431263964619 29154684847310146895946929)
                  ·
                    refine ⟨21866013635482610171960197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29154684847310146895946929 21866013635482610171960197)
                    ·
                      refine ⟨4099877556652989407242537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21866013635482610171960197 4099877556652989407242537)
                      ·
                        rfl

theorem cell23_7984483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7984483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984483 prefixEnd_7984483 := by exact prefixLift 7984483
  have htrace : WordTrace (prefixWord ++ tailWord_7984483) baseStart_7984483 baseEnd_7984483 := by
    simpa [prefixWord, tailWord_7984483, baseEnd_7984483] using wordTrace_append hprefix tailTrace_7984483
  have hstable : (prefixWord ++ tailWord_7984483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984483).length < 2 ^ (prefixWord ++ tailWord_7984483).sum := by decide
  have hdescent : baseEnd_7984483 < baseStart_7984483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984493 : List Nat := [1, 5, 1, 1, 1, 3, 4, 7]
def baseStart_7984493 : Nat := 118140960795 + 7984493 * 2 ^ 59
def prefixEnd_7984493 : Nat := 4983230072969 + 3 ^ 40 * 7984493 * 2
def baseEnd_7984493 : Nat := 151847507091093865485833

theorem tailTrace_7984493 : CollatzResearch.WordTrace tailWord_7984493 prefixEnd_7984493 151847507091093865485833 := by
  unfold tailWord_7984493
  simp only [CollatzResearch.WordTrace]
  refine ⟨291218384262552978684358133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194145589508368652456238755 291218384262552978684358133)
  ·
    refine ⟨27301723524614341751658575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291218384262552978684358133 27301723524614341751658575)
    ·
      refine ⟨40952585286921512627487863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301723524614341751658575 40952585286921512627487863)
      ·
        refine ⟨61428877930382268941231795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40952585286921512627487863 61428877930382268941231795)
        ·
          refine ⟨92143316895573403411847693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61428877930382268941231795 92143316895573403411847693)
          ·
            refine ⟨34553743835840026279442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92143316895573403411847693 34553743835840026279442885)
            ·
              refine ⟨6478826969220004927395541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34553743835840026279442885 6478826969220004927395541)
              ·
                refine ⟨151847507091093865485833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6478826969220004927395541 151847507091093865485833)
                ·
                  rfl

theorem cell23_7984493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 7].length) (baseStart_7984493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984493 prefixEnd_7984493 := by exact prefixLift 7984493
  have htrace : WordTrace (prefixWord ++ tailWord_7984493) baseStart_7984493 baseEnd_7984493 := by
    simpa [prefixWord, tailWord_7984493, baseEnd_7984493] using wordTrace_append hprefix tailTrace_7984493
  have hstable : (prefixWord ++ tailWord_7984493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984493).length < 2 ^ (prefixWord ++ tailWord_7984493).sum := by decide
  have hdescent : baseEnd_7984493 < baseStart_7984493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984503 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_7984503 : Nat := 118140960795 + 7984503 * 2 ^ 59
def prefixEnd_7984503 : Nat := 4983230072969 + 3 ^ 40 * 7984503 * 2
def baseEnd_7984503 : Nat := 4099887826266079328992445

theorem tailTrace_7984503 : CollatzResearch.WordTrace tailWord_7984503 prefixEnd_7984503 4099887826266079328992445 := by
  unfold tailWord_7984503
  simp only [CollatzResearch.WordTrace]
  refine ⟨291218748992516750392222163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194145832661677833594814775 291218748992516750392222163)
  ·
    refine ⟨436828123488775125588333245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291218748992516750392222163 436828123488775125588333245)
    ·
      refine ⟨163810546308290672095624967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436828123488775125588333245 163810546308290672095624967)
      ·
        refine ⟨245715819462436008143437451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163810546308290672095624967 245715819462436008143437451)
        ·
          refine ⟨368573729193654012215156177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245715819462436008143437451 368573729193654012215156177)
          ·
            refine ⟨276430296895240509161367133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368573729193654012215156177 276430296895240509161367133)
            ·
              refine ⟨103661361335715190935512675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276430296895240509161367133 103661361335715190935512675)
              ·
                refine ⟨155492042003572786403269013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103661361335715190935512675 155492042003572786403269013)
                ·
                  refine ⟨7288689468917474362653235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155492042003572786403269013 7288689468917474362653235)
                  ·
                    refine ⟨10933034203376211543979853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288689468917474362653235 10933034203376211543979853)
                    ·
                      refine ⟨4099887826266079328992445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10933034203376211543979853 4099887826266079328992445)
                      ·
                        rfl

theorem cell23_7984503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_7984503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984503 prefixEnd_7984503 := by exact prefixLift 7984503
  have htrace : WordTrace (prefixWord ++ tailWord_7984503) baseStart_7984503 baseEnd_7984503 := by
    simpa [prefixWord, tailWord_7984503, baseEnd_7984503] using wordTrace_append hprefix tailTrace_7984503
  have hstable : (prefixWord ++ tailWord_7984503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984503).length < 2 ^ (prefixWord ++ tailWord_7984503).sum := by decide
  have hdescent : baseEnd_7984503 < baseStart_7984503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984520 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7984520 : Nat := 118140960795 + 7984520 * 2 ^ 59
def prefixEnd_7984520 : Nat := 4983230072969 + 3 ^ 40 * 7984520 * 2
def baseEnd_7984520 : Nat := 4099896555437205762479867

theorem tailTrace_7984520 : CollatzResearch.WordTrace tailWord_7984520 prefixEnd_7984520 4099896555437205762479867 := by
  unfold tailWord_7984520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145609684516727581147795507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194146246022303441530394009 145609684516727581147795507)
  ·
    refine ⟨218414526775091371721693261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145609684516727581147795507 218414526775091371721693261)
    ·
      refine ⟨81905447540659264395634973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218414526775091371721693261 81905447540659264395634973)
      ·
        refine ⟨30714542827747224148363115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81905447540659264395634973 30714542827747224148363115)
        ·
          refine ⟨46071814241620836222544673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714542827747224148363115 46071814241620836222544673)
          ·
            refine ⟨34553860681215627166908505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46071814241620836222544673 34553860681215627166908505)
            ·
              refine ⟨25915395510911720375181379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34553860681215627166908505 25915395510911720375181379)
              ·
                refine ⟨38873093266367580562772069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25915395510911720375181379 38873093266367580562772069)
                ·
                  refine ⟨7288704987443921355519763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38873093266367580562772069 7288704987443921355519763)
                  ·
                    refine ⟨10933057481165882033279645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288704987443921355519763 10933057481165882033279645)
                    ·
                      refine ⟨4099896555437205762479867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10933057481165882033279645 4099896555437205762479867)
                      ·
                        rfl

theorem cell23_7984520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7984520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984520 prefixEnd_7984520 := by exact prefixLift 7984520
  have htrace : WordTrace (prefixWord ++ tailWord_7984520) baseStart_7984520 baseEnd_7984520 := by
    simpa [prefixWord, tailWord_7984520, baseEnd_7984520] using wordTrace_append hprefix tailTrace_7984520
  have hstable : (prefixWord ++ tailWord_7984520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984520).length < 2 ^ (prefixWord ++ tailWord_7984520).sum := by decide
  have hdescent : baseEnd_7984520 < baseStart_7984520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984521 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 1, 2, 2]
def baseStart_7984521 : Nat := 118140960795 + 7984521 * 2 ^ 59
def prefixEnd_7984521 : Nat := 4983230072969 + 3 ^ 40 * 7984521 * 2
def baseEnd_7984521 : Nat := 4099897068917860258567363

theorem tailTrace_7984521 : CollatzResearch.WordTrace tailWord_7984521 prefixEnd_7984521 4099897068917860258567363 := by
  unfold tailWord_7984521
  simp only [CollatzResearch.WordTrace]
  refine ⟨291219405506451539466377417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194146270337634359644251611 291219405506451539466377417)
  ·
    refine ⟨218414554129838654599783063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291219405506451539466377417 218414554129838654599783063)
    ·
      refine ⟨327621831194757981899674595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218414554129838654599783063 327621831194757981899674595)
      ·
        refine ⟨491432746792136972849511893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327621831194757981899674595 491432746792136972849511893)
        ·
          refine ⟨11517955002940710301160435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 491432746792136972849511893 11517955002940710301160435)
          ·
            refine ⟨17276932504411065451740653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517955002940710301160435 17276932504411065451740653)
            ·
              refine ⟨6478849689154149544402745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17276932504411065451740653 6478849689154149544402745)
              ·
                refine ⟨4859137266865612158302059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478849689154149544402745 4859137266865612158302059)
                ·
                  refine ⟨7288705900298418237453089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859137266865612158302059 7288705900298418237453089)
                  ·
                    refine ⟨5466529425223813678089817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7288705900298418237453089 5466529425223813678089817)
                    ·
                      refine ⟨4099897068917860258567363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466529425223813678089817 4099897068917860258567363)
                      ·
                        rfl

theorem cell23_7984521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 1, 2, 2].length) (baseStart_7984521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984521 prefixEnd_7984521 := by exact prefixLift 7984521
  have htrace : WordTrace (prefixWord ++ tailWord_7984521) baseStart_7984521 baseEnd_7984521 := by
    simpa [prefixWord, tailWord_7984521, baseEnd_7984521] using wordTrace_append hprefix tailTrace_7984521
  have hstable : (prefixWord ++ tailWord_7984521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984521).length < 2 ^ (prefixWord ++ tailWord_7984521).sum := by decide
  have hdescent : baseEnd_7984521 < baseStart_7984521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984537 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 2, 1, 3]
def baseStart_7984537 : Nat := 118140960795 + 7984537 * 2 ^ 59
def prefixEnd_7984537 : Nat := 4983230072969 + 3 ^ 40 * 7984537 * 2
def baseEnd_7984537 : Nat := 4099905284608332195967289

theorem tailTrace_7984537 : CollatzResearch.WordTrace tailWord_7984537 prefixEnd_7984537 4099905284608332195967289 := by
  unfold tailWord_7984537
  simp only [CollatzResearch.WordTrace]
  refine ⟨291219989074393574198959865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194146659382929049465973243 291219989074393574198959865)
  ·
    refine ⟨218414991805795180649219899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291219989074393574198959865 218414991805795180649219899)
    ·
      refine ⟨327622487708692770973829849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218414991805795180649219899 327622487708692770973829849)
      ·
        refine ⟨245716865781519578230372387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327622487708692770973829849 245716865781519578230372387)
        ·
          refine ⟨368575298672279367345558581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245716865781519578230372387 368575298672279367345558581)
          ·
            refine ⟨34553934250526190688646117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368575298672279367345558581 34553934250526190688646117)
            ·
              refine ⟨6478862671973660754121147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34553934250526190688646117 6478862671973660754121147)
              ·
                refine ⟨9718294007960491131181721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478862671973660754121147 9718294007960491131181721)
                ·
                  refine ⟨7288720505970368348386291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718294007960491131181721 7288720505970368348386291)
                  ·
                    refine ⟨10933080758955552522579437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288720505970368348386291 10933080758955552522579437)
                    ·
                      refine ⟨4099905284608332195967289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10933080758955552522579437 4099905284608332195967289)
                      ·
                        rfl

theorem cell23_7984537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_7984537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984537 prefixEnd_7984537 := by exact prefixLift 7984537
  have htrace : WordTrace (prefixWord ++ tailWord_7984537) baseStart_7984537 baseEnd_7984537 := by
    simpa [prefixWord, tailWord_7984537, baseEnd_7984537] using wordTrace_append hprefix tailTrace_7984537
  have hstable : (prefixWord ++ tailWord_7984537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984537).length < 2 ^ (prefixWord ++ tailWord_7984537).sum := by decide
  have hdescent : baseEnd_7984537 < baseStart_7984537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984560 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2]
def baseStart_7984560 : Nat := 118140960795 + 7984560 * 2 ^ 59
def prefixEnd_7984560 : Nat := 4983230072969 + 3 ^ 40 * 7984560 * 2
def baseEnd_7984560 : Nat := 4099917094663385605979683

theorem tailTrace_7984560 : CollatzResearch.WordTrace tailWord_7984560 prefixEnd_7984560 4099917094663385605979683 := by
  unfold tailWord_7984560
  simp only [CollatzResearch.WordTrace]
  refine ⟨145610413976655124563523567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194147218635540166084698089 145610413976655124563523567)
  ·
    refine ⟨218415620964982686845285351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145610413976655124563523567 218415620964982686845285351)
    ·
      refine ⟨327623431447474030267928027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218415620964982686845285351 327623431447474030267928027)
      ·
        refine ⟨491435147171211045401892041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327623431447474030267928027 491435147171211045401892041)
        ·
          refine ⟨368576360378408284051419031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491435147171211045401892041 368576360378408284051419031)
          ·
            refine ⟨552864540567612426077128547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368576360378408284051419031 552864540567612426077128547)
            ·
              refine ⟨829296810851418639115692821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552864540567612426077128547 829296810851418639115692821)
              ·
                refine ⟨38873288008660248708548101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 829296810851418639115692821 38873288008660248708548101)
                ·
                  refine ⟨7288741501623796632852769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38873288008660248708548101 7288741501623796632852769)
                  ·
                    refine ⟨5466556126217847474639577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7288741501623796632852769 5466556126217847474639577)
                    ·
                      refine ⟨4099917094663385605979683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466556126217847474639577 4099917094663385605979683)
                      ·
                        rfl

theorem cell23_7984560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4, 2, 2].length) (baseStart_7984560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984560 prefixEnd_7984560 := by exact prefixLift 7984560
  have htrace : WordTrace (prefixWord ++ tailWord_7984560) baseStart_7984560 baseEnd_7984560 := by
    simpa [prefixWord, tailWord_7984560, baseEnd_7984560] using wordTrace_append hprefix tailTrace_7984560
  have hstable : (prefixWord ++ tailWord_7984560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984560).length < 2 ^ (prefixWord ++ tailWord_7984560).sum := by decide
  have hdescent : baseEnd_7984560 < baseStart_7984560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984573 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7984573 : Nat := 118140960795 + 7984573 * 2 ^ 59
def prefixEnd_7984573 : Nat := 4983230072969 + 3 ^ 40 * 7984573 * 2
def baseEnd_7984573 : Nat := 4099923769911894055117123

theorem tailTrace_7984573 : CollatzResearch.WordTrace tailWord_7984573 prefixEnd_7984573 4099923769911894055117123 := by
  unfold tailWord_7984573
  simp only [CollatzResearch.WordTrace]
  refine ⟨291221302102263152347270373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194147534734842101564846915 291221302102263152347270373)
  ·
    refine ⟨54603994144174341065113195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291221302102263152347270373 54603994144174341065113195)
    ·
      refine ⟨81905991216261511597669793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54603994144174341065113195 81905991216261511597669793)
      ·
        refine ⟨61429493412196133698252345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81905991216261511597669793 61429493412196133698252345)
        ·
          refine ⟨46072120059147100273689259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61429493412196133698252345 46072120059147100273689259)
          ·
            refine ⟨69108180088720650410533889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46072120059147100273689259 69108180088720650410533889)
            ·
              refine ⟨51831135066540487807900417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69108180088720650410533889 51831135066540487807900417)
              ·
                refine ⟨38873351299905365855925313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51831135066540487807900417 38873351299905365855925313)
                ·
                  refine ⟨29155013474929024391943985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38873351299905365855925313 29155013474929024391943985)
                  ·
                    refine ⟨21866260106196768293957989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29155013474929024391943985 21866260106196768293957989)
                    ·
                      refine ⟨4099923769911894055117123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21866260106196768293957989 4099923769911894055117123)
                      ·
                        rfl

theorem cell23_7984573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7984573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984573 prefixEnd_7984573 := by exact prefixLift 7984573
  have htrace : WordTrace (prefixWord ++ tailWord_7984573) baseStart_7984573 baseEnd_7984573 := by
    simpa [prefixWord, tailWord_7984573, baseEnd_7984573] using wordTrace_append hprefix tailTrace_7984573
  have hstable : (prefixWord ++ tailWord_7984573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984573).length < 2 ^ (prefixWord ++ tailWord_7984573).sum := by decide
  have hdescent : baseEnd_7984573 < baseStart_7984573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984576 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_7984576 : Nat := 118140960795 + 7984576 * 2 ^ 59
def prefixEnd_7984576 : Nat := 4983230072969 + 3 ^ 40 * 7984576 * 2
def baseEnd_7984576 : Nat := 4099925310353857543379609

theorem tailTrace_7984576 : CollatzResearch.WordTrace tailWord_7984576 prefixEnd_7984576 4099925310353857543379609 := by
  unfold tailWord_7984576
  simp only [CollatzResearch.WordTrace]
  refine ⟨145610705760626141929814791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194147607680834855906419721 145610705760626141929814791)
  ·
    refine ⟨218416058640939212894722187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145610705760626141929814791 218416058640939212894722187)
    ·
      refine ⟨327624087961408819342083281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218416058640939212894722187 327624087961408819342083281)
      ·
        refine ⟨245718065971056614506562461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327624087961408819342083281 245718065971056614506562461)
        ·
          refine ⟨92144274739146230439960923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245718065971056614506562461 92144274739146230439960923)
          ·
            refine ⟨138216412108719345659941385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92144274739146230439960923 138216412108719345659941385)
            ·
              refine ⟨103662309081539509244956039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138216412108719345659941385 103662309081539509244956039)
              ·
                refine ⟨155493463622309263867434059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103662309081539509244956039 155493463622309263867434059)
                ·
                  refine ⟨233240195433463895801151089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155493463622309263867434059 233240195433463895801151089)
                  ·
                    refine ⟨174930146575097921850863317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233240195433463895801151089 174930146575097921850863317)
                    ·
                      refine ⟨4099925310353857543379609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174930146575097921850863317 4099925310353857543379609)
                      ·
                        rfl

theorem cell23_7984576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_7984576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984576 prefixEnd_7984576 := by exact prefixLift 7984576
  have htrace : WordTrace (prefixWord ++ tailWord_7984576) baseStart_7984576 baseEnd_7984576 := by
    simpa [prefixWord, tailWord_7984576, baseEnd_7984576] using wordTrace_append hprefix tailTrace_7984576
  have hstable : (prefixWord ++ tailWord_7984576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984576).length < 2 ^ (prefixWord ++ tailWord_7984576).sum := by decide
  have hdescent : baseEnd_7984576 < baseStart_7984576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984580 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7984580 : Nat := 118140960795 + 7984580 * 2 ^ 59
def prefixEnd_7984580 : Nat := 4983230072969 + 3 ^ 40 * 7984580 * 2
def baseEnd_7984580 : Nat := 4099927364276475527729591

theorem tailTrace_7984580 : CollatzResearch.WordTrace tailWord_7984580 prefixEnd_7984580 4099927364276475527729591 := by
  unfold tailWord_7984580
  simp only [CollatzResearch.WordTrace]
  refine ⟨145610778706618896271387597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194147704942158528361850129 145610778706618896271387597)
  ·
    refine ⟨54604042014982086101770349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145610778706618896271387597 54604042014982086101770349)
    ·
      refine ⟨20476515755618282288163881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54604042014982086101770349 20476515755618282288163881)
      ·
        refine ⟨15357386816713711716122911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20476515755618282288163881 15357386816713711716122911)
        ·
          refine ⟨23036080225070567574184367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357386816713711716122911 23036080225070567574184367)
          ·
            refine ⟨34554120337605851361276551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23036080225070567574184367 34554120337605851361276551)
            ·
              refine ⟨51831180506408777041914827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34554120337605851361276551 51831180506408777041914827)
              ·
                refine ⟨77746770759613165562872241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51831180506408777041914827 77746770759613165562872241)
                ·
                  refine ⟨58310078069709874172154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77746770759613165562872241 58310078069709874172154181)
                  ·
                    refine ⟨10933139638070601407278909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58310078069709874172154181 10933139638070601407278909)
                    ·
                      refine ⟨4099927364276475527729591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10933139638070601407278909 4099927364276475527729591)
                      ·
                        rfl

theorem cell23_7984580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7984580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984580 prefixEnd_7984580 := by exact prefixLift 7984580
  have htrace : WordTrace (prefixWord ++ tailWord_7984580) baseStart_7984580 baseEnd_7984580 := by
    simpa [prefixWord, tailWord_7984580, baseEnd_7984580] using wordTrace_append hprefix tailTrace_7984580
  have hstable : (prefixWord ++ tailWord_7984580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984580).length < 2 ^ (prefixWord ++ tailWord_7984580).sum := by decide
  have hdescent : baseEnd_7984580 < baseStart_7984580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984633 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_7984633 : Nat := 118140960795 + 7984633 * 2 ^ 59
def prefixEnd_7984633 : Nat := 4983230072969 + 3 ^ 40 * 7984633 * 2
def baseEnd_7984633 : Nat := 4099954578751163820366847

theorem tailTrace_7984633 : CollatzResearch.WordTrace tailWord_7984633 prefixEnd_7984633 4099954578751163820366847 := by
  unfold tailWord_7984633
  simp only [CollatzResearch.WordTrace]
  refine ⟨291223490482045782594454553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194148993654697188396303035 291223490482045782594454553)
  ·
    refine ⟨218417617861534336945840915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291223490482045782594454553 218417617861534336945840915)
    ·
      refine ⟨327626426792301505418761373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218417617861534336945840915 327626426792301505418761373)
      ·
        refine ⟨122859910047113064532035515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327626426792301505418761373 122859910047113064532035515)
        ·
          refine ⟨184289865070669596798053273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122859910047113064532035515 184289865070669596798053273)
          ·
            refine ⟨138217398803002197598539955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184289865070669596798053273 138217398803002197598539955)
            ·
              refine ⟨207326098204503296397809933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138217398803002197598539955 207326098204503296397809933)
              ·
                refine ⟨77747286826688736149178725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207326098204503296397809933 77747286826688736149178725)
                ·
                  refine ⟨14577616280004138027971011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77747286826688736149178725 14577616280004138027971011)
                  ·
                    refine ⟨21866424420006207041956517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14577616280004138027971011 21866424420006207041956517)
                    ·
                      refine ⟨4099954578751163820366847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21866424420006207041956517 4099954578751163820366847)
                      ·
                        rfl

theorem cell23_7984633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_7984633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984633 prefixEnd_7984633 := by exact prefixLift 7984633
  have htrace : WordTrace (prefixWord ++ tailWord_7984633) baseStart_7984633 baseEnd_7984633 := by
    simpa [prefixWord, tailWord_7984633, baseEnd_7984633] using wordTrace_append hprefix tailTrace_7984633
  have hstable : (prefixWord ++ tailWord_7984633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984633).length < 2 ^ (prefixWord ++ tailWord_7984633).sum := by decide
  have hdescent : baseEnd_7984633 < baseStart_7984633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984673 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 8]
def baseStart_7984673 : Nat := 118140960795 + 7984673 * 2 ^ 59
def prefixEnd_7984673 : Nat := 4983230072969 + 3 ^ 40 * 7984673 * 2
def baseEnd_7984673 : Nat := 455552790886371518207407

theorem tailTrace_7984673 : CollatzResearch.WordTrace tailWord_7984673 prefixEnd_7984673 455552790886371518207407 := by
  unfold tailWord_7984673
  simp only [CollatzResearch.WordTrace]
  refine ⟨291224949401900869425910673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194149966267933912950607115 291224949401900869425910673)
  ·
    refine ⟨218418712051425652069433005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291224949401900869425910673 218418712051425652069433005)
    ·
      refine ⟨81907017019284619526037377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218418712051425652069433005 81907017019284619526037377)
      ·
        refine ⟨61430262764463464644528033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81907017019284619526037377 61430262764463464644528033)
        ·
          refine ⟨46072697073347598483396025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61430262764463464644528033 46072697073347598483396025)
          ·
            refine ⟨34554522805010698862547019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46072697073347598483396025 34554522805010698862547019)
            ·
              refine ⟨51831784207516048293820529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34554522805010698862547019 51831784207516048293820529)
              ·
                refine ⟨38873838155637036220365397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51831784207516048293820529 38873838155637036220365397)
                ·
                  refine ⟨455552790886371518207407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38873838155637036220365397 455552790886371518207407)
                  ·
                    rfl

theorem cell23_7984673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_7984673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984673 prefixEnd_7984673 := by exact prefixLift 7984673
  have htrace : WordTrace (prefixWord ++ tailWord_7984673) baseStart_7984673 baseEnd_7984673 := by
    simpa [prefixWord, tailWord_7984673, baseEnd_7984673] using wordTrace_append hprefix tailTrace_7984673
  have hstable : (prefixWord ++ tailWord_7984673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984673).length < 2 ^ (prefixWord ++ tailWord_7984673).sum := by decide
  have hdescent : baseEnd_7984673 < baseStart_7984673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984727 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_7984727 : Nat := 118140960795 + 7984727 * 2 ^ 59
def prefixEnd_7984727 : Nat := 4983230072969 + 3 ^ 40 * 7984727 * 2
def baseEnd_7984727 : Nat := 4100002845932686452591415

theorem tailTrace_7984727 : CollatzResearch.WordTrace tailWord_7984727 prefixEnd_7984727 4100002845932686452591415 := by
  unfold tailWord_7984727
  simp only [CollatzResearch.WordTrace]
  refine ⟨291226918943705236648376435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194151279295803491098917623 291226918943705236648376435)
  ·
    refine ⟨436840378415557854972564653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291226918943705236648376435 436840378415557854972564653)
    ·
      refine ⟨163815141905834195614711745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436840378415557854972564653 163815141905834195614711745)
      ·
        refine ⟨122861356429375646711033809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163815141905834195614711745 122861356429375646711033809)
        ·
          refine ⟨92146017322031735033275357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122861356429375646711033809 92146017322031735033275357)
          ·
            refine ⟨34554756495761900637478259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92146017322031735033275357 34554756495761900637478259)
            ·
              refine ⟨51832134743642850956217389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34554756495761900637478259 51832134743642850956217389)
              ·
                refine ⟨19437050528866069108581521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51832134743642850956217389 19437050528866069108581521)
                ·
                  refine ⟨14577787896649551831436141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19437050528866069108581521 14577787896649551831436141)
                  ·
                    refine ⟨5466670461243581936788553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14577787896649551831436141 5466670461243581936788553)
                    ·
                      refine ⟨4100002845932686452591415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466670461243581936788553 4100002845932686452591415)
                      ·
                        rfl

theorem cell23_7984727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_7984727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984727 prefixEnd_7984727 := by exact prefixLift 7984727
  have htrace : WordTrace (prefixWord ++ tailWord_7984727) baseStart_7984727 baseEnd_7984727 := by
    simpa [prefixWord, tailWord_7984727, baseEnd_7984727] using wordTrace_append hprefix tailTrace_7984727
  have hstable : (prefixWord ++ tailWord_7984727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984727).length < 2 ^ (prefixWord ++ tailWord_7984727).sum := by decide
  have hdescent : baseEnd_7984727 < baseStart_7984727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984737 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7984737 : Nat := 118140960795 + 7984737 * 2 ^ 59
def prefixEnd_7984737 : Nat := 4983230072969 + 3 ^ 40 * 7984737 * 2
def baseEnd_7984737 : Nat := 1366669326913077137822123

theorem tailTrace_7984737 : CollatzResearch.WordTrace tailWord_7984737 prefixEnd_7984737 1366669326913077137822123 := by
  unfold tailWord_7984737
  simp only [CollatzResearch.WordTrace]
  refine ⟨291227283673669008356240465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194151522449112672237493643 291227283673669008356240465)
  ·
    refine ⟨218420462755251756267180349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291227283673669008356240465 218420462755251756267180349)
    ·
      refine ⟨81907673533219408600192631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218420462755251756267180349 81907673533219408600192631)
      ·
        refine ⟨122861510299829112900288947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81907673533219408600192631 122861510299829112900288947)
        ·
          refine ⟨184292265449743669350433421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122861510299829112900288947 184292265449743669350433421)
          ·
            refine ⟨69109599543653876006412533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184292265449743669350433421 69109599543653876006412533)
            ·
              refine ⟨6479024957217550875601175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69109599543653876006412533 6479024957217550875601175)
              ·
                refine ⟨9718537435826326313401763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479024957217550875601175 9718537435826326313401763)
                ·
                  refine ⟨14577806153739489470102645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9718537435826326313401763 14577806153739489470102645)
                  ·
                    refine ⟨1366669326913077137822123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14577806153739489470102645 1366669326913077137822123)
                    ·
                      rfl

theorem cell23_7984737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7984737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984737 prefixEnd_7984737 := by exact prefixLift 7984737
  have htrace : WordTrace (prefixWord ++ tailWord_7984737) baseStart_7984737 baseEnd_7984737 := by
    simpa [prefixWord, tailWord_7984737, baseEnd_7984737] using wordTrace_append hprefix tailTrace_7984737
  have hstable : (prefixWord ++ tailWord_7984737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984737).length < 2 ^ (prefixWord ++ tailWord_7984737).sum := by decide
  have hdescent : baseEnd_7984737 < baseStart_7984737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984744 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7984744 : Nat := 118140960795 + 7984744 * 2 ^ 59
def prefixEnd_7984744 : Nat := 4983230072969 + 3 ^ 40 * 7984744 * 2
def baseEnd_7984744 : Nat := 4100011575103812886078837

theorem tailTrace_7984744 : CollatzResearch.WordTrace tailWord_7984744 prefixEnd_7984744 4100011575103812886078837 := by
  unfold tailWord_7984744
  simp only [CollatzResearch.WordTrace]
  refine ⟨145613769492321824275872643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194151692656429099034496857 145613769492321824275872643)
  ·
    refine ⟨218420654238482736413808965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145613769492321824275872643 218420654238482736413808965)
    ·
      refine ⟨40953872669715513077589181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218420654238482736413808965 40953872669715513077589181)
      ·
        refine ⟨15357702251143317404095943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40953872669715513077589181 15357702251143317404095943)
        ·
          refine ⟨23036553376714976106143915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357702251143317404095943 23036553376714976106143915)
          ·
            refine ⟨34554830065072464159215873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23036553376714976106143915 34554830065072464159215873)
            ·
              refine ⟨25916122548804348119411905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34554830065072464159215873 25916122548804348119411905)
              ·
                refine ⟨19437091911603261089558929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25916122548804348119411905 19437091911603261089558929)
                ·
                  refine ⟨14577818933702445817169197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19437091911603261089558929 14577818933702445817169197)
                  ·
                    refine ⟨5466682100138417181438449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14577818933702445817169197 5466682100138417181438449)
                    ·
                      refine ⟨4100011575103812886078837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466682100138417181438449 4100011575103812886078837)
                      ·
                        rfl

theorem cell23_7984744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7984744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984744 prefixEnd_7984744 := by exact prefixLift 7984744
  have htrace : WordTrace (prefixWord ++ tailWord_7984744) baseStart_7984744 baseEnd_7984744 := by
    simpa [prefixWord, tailWord_7984744, baseEnd_7984744] using wordTrace_append hprefix tailTrace_7984744
  have hstable : (prefixWord ++ tailWord_7984744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984744).length < 2 ^ (prefixWord ++ tailWord_7984744).sum := by decide
  have hdescent : baseEnd_7984744 < baseStart_7984744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984753 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_7984753 : Nat := 118140960795 + 7984753 * 2 ^ 59
def prefixEnd_7984753 : Nat := 4983230072969 + 3 ^ 40 * 7984753 * 2
def baseEnd_7984753 : Nat := 4100016196429703350866295

theorem tailTrace_7984753 : CollatzResearch.WordTrace tailWord_7984753 prefixEnd_7984753 4100016196429703350866295 := by
  unfold tailWord_7984753
  simp only [CollatzResearch.WordTrace]
  refine ⟨291227867241611043088822913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194151911494407362059215275 291227867241611043088822913)
  ·
    refine ⟨218420900431208282316617185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291227867241611043088822913 218420900431208282316617185)
    ·
      refine ⟨163815675323406211737462889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218420900431208282316617185 163815675323406211737462889)
      ·
        refine ⟨122861756492554658803097167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163815675323406211737462889 122861756492554658803097167)
        ·
          refine ⟨184292634738831988204645751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122861756492554658803097167 184292634738831988204645751)
          ·
            refine ⟨276438952108247982306968627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184292634738831988204645751 276438952108247982306968627)
            ·
              refine ⟨414658428162371973460452941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276438952108247982306968627 414658428162371973460452941)
              ·
                refine ⟨155496910560889490047669853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414658428162371973460452941 155496910560889490047669853)
                ·
                  refine ⟨58311341460333558767876195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155496910560889490047669853 58311341460333558767876195)
                  ·
                    refine ⟨87467012190500338151814293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58311341460333558767876195 87467012190500338151814293)
                    ·
                      refine ⟨4100016196429703350866295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87467012190500338151814293 4100016196429703350866295)
                      ·
                        rfl

theorem cell23_7984753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_7984753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984753 prefixEnd_7984753 := by exact prefixLift 7984753
  have htrace : WordTrace (prefixWord ++ tailWord_7984753) baseStart_7984753 baseEnd_7984753 := by
    simpa [prefixWord, tailWord_7984753, baseEnd_7984753] using wordTrace_append hprefix tailTrace_7984753
  have hstable : (prefixWord ++ tailWord_7984753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984753).length < 2 ^ (prefixWord ++ tailWord_7984753).sum := by decide
  have hdescent : baseEnd_7984753 < baseStart_7984753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984757 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7984757 : Nat := 118140960795 + 7984757 * 2 ^ 59
def prefixEnd_7984757 : Nat := 4983230072969 + 3 ^ 40 * 7984757 * 2
def baseEnd_7984757 : Nat := 4100018250352321335216277

theorem tailTrace_7984757 : CollatzResearch.WordTrace tailWord_7984757 prefixEnd_7984757 4100018250352321335216277 := by
  unfold tailWord_7984757
  simp only [CollatzResearch.WordTrace]
  refine ⟨291228013133596551771968525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194152008755731034514645683 291228013133596551771968525)
  ·
    refine ⟨109210504925098706914488197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291228013133596551771968525 109210504925098706914488197)
    ·
      refine ⟨20476969673456007546466537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109210504925098706914488197 20476969673456007546466537)
      ·
        refine ⟨15357727255092005659849903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20476969673456007546466537 15357727255092005659849903)
        ·
          refine ⟨23036590882638008489774855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357727255092005659849903 23036590882638008489774855)
          ·
            refine ⟨34554886323957012734662283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23036590882638008489774855 34554886323957012734662283)
            ·
              refine ⟨51832329485935519101993425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34554886323957012734662283 51832329485935519101993425)
              ·
                refine ⟨38874247114451639326495069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51832329485935519101993425 38874247114451639326495069)
                ·
                  refine ⟨14577842667919364747435651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38874247114451639326495069 14577842667919364747435651)
                  ·
                    refine ⟨21866764001879047121153477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14577842667919364747435651 21866764001879047121153477)
                    ·
                      refine ⟨4100018250352321335216277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21866764001879047121153477 4100018250352321335216277)
                      ·
                        rfl

theorem cell23_7984757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7984757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984757 prefixEnd_7984757 := by exact prefixLift 7984757
  have htrace : WordTrace (prefixWord ++ tailWord_7984757) baseStart_7984757 baseEnd_7984757 := by
    simpa [prefixWord, tailWord_7984757, baseEnd_7984757] using wordTrace_append hprefix tailTrace_7984757
  have hstable : (prefixWord ++ tailWord_7984757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984757).length < 2 ^ (prefixWord ++ tailWord_7984757).sum := by decide
  have hdescent : baseEnd_7984757 < baseStart_7984757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984780 : List Nat := [2, 2, 1, 2, 1, 1, 7, 7]
def baseStart_7984780 : Nat := 118140960795 + 7984780 * 2 ^ 59
def prefixEnd_7984780 : Nat := 4983230072969 + 3 ^ 40 * 7984780 * 2
def baseEnd_7984780 : Nat := 151852965200273138712173

theorem tailTrace_7984780 : CollatzResearch.WordTrace tailWord_7984780 prefixEnd_7984780 151852965200273138712173 := by
  unfold tailWord_7984780
  simp only [CollatzResearch.WordTrace]
  refine ⟨145614426006256613350027897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194152568008342151133370529 145614426006256613350027897)
  ·
    refine ⟨109210819504692460012520923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145614426006256613350027897 109210819504692460012520923)
    ·
      refine ⟨163816229257038690018781385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109210819504692460012520923 163816229257038690018781385)
      ·
        refine ⟨122862171942779017514086039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163816229257038690018781385 122862171942779017514086039)
        ·
          refine ⟨184293257914168526271129059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122862171942779017514086039 184293257914168526271129059)
          ·
            refine ⟨276439886871252789406693589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184293257914168526271129059 276439886871252789406693589)
            ·
              refine ⟨6479059848544987251719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276439886871252789406693589 6479059848544987251719381)
              ·
                refine ⟨151852965200273138712173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6479059848544987251719381 151852965200273138712173)
                ·
                  rfl

theorem cell23_7984780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 7].length) (baseStart_7984780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984780 prefixEnd_7984780 := by exact prefixLift 7984780
  have htrace : WordTrace (prefixWord ++ tailWord_7984780) baseStart_7984780 baseEnd_7984780 := by
    simpa [prefixWord, tailWord_7984780, baseEnd_7984780] using wordTrace_append hprefix tailTrace_7984780
  have hstable : (prefixWord ++ tailWord_7984780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984780).length < 2 ^ (prefixWord ++ tailWord_7984780).sum := by decide
  have hdescent : baseEnd_7984780 < baseStart_7984780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984788 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7984788 : Nat := 118140960795 + 7984788 * 2 ^ 59
def prefixEnd_7984788 : Nat := 4983230072969 + 3 ^ 40 * 7984788 * 2
def baseEnd_7984788 : Nat := 1366678056084203571309545

theorem tailTrace_7984788 : CollatzResearch.WordTrace tailWord_7984788 prefixEnd_7984788 1366678056084203571309545 := by
  unfold tailWord_7984788
  simp only [CollatzResearch.WordTrace]
  refine ⟨145614571898242122033173509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194152762530989496044231345 145614571898242122033173509)
  ·
    refine ⟨27302732230920397881220033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145614571898242122033173509 27302732230920397881220033)
    ·
      refine ⟨20477049173190298410915025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27302732230920397881220033 20477049173190298410915025)
      ·
        refine ⟨15357786879892723808186269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20477049173190298410915025 15357786879892723808186269)
        ·
          refine ⟨5759170079959771428069851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15357786879892723808186269 5759170079959771428069851)
          ·
            refine ⟨8638755119939657142104777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759170079959771428069851 8638755119939657142104777)
            ·
              refine ⟨6479066339954742856578583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638755119939657142104777 6479066339954742856578583)
              ·
                refine ⟨9718599509932114284867875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479066339954742856578583 9718599509932114284867875)
                ·
                  refine ⟨14577899264898171427301813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9718599509932114284867875 14577899264898171427301813)
                  ·
                    refine ⟨1366678056084203571309545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14577899264898171427301813 1366678056084203571309545)
                    ·
                      rfl

theorem cell23_7984788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7984788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984788 prefixEnd_7984788 := by exact prefixLift 7984788
  have htrace : WordTrace (prefixWord ++ tailWord_7984788) baseStart_7984788 baseEnd_7984788 := by
    simpa [prefixWord, tailWord_7984788, baseEnd_7984788] using wordTrace_append hprefix tailTrace_7984788
  have hstable : (prefixWord ++ tailWord_7984788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984788).length < 2 ^ (prefixWord ++ tailWord_7984788).sum := by decide
  have hdescent : baseEnd_7984788 < baseStart_7984788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984791 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7984791 : Nat := 118140960795 + 7984791 * 2 ^ 59
def prefixEnd_7984791 : Nat := 4983230072969 + 3 ^ 40 * 7984791 * 2
def baseEnd_7984791 : Nat := 4100035708694574202191121

theorem tailTrace_7984791 : CollatzResearch.WordTrace tailWord_7984791 prefixEnd_7984791 4100035708694574202191121 := by
  unfold tailWord_7984791
  simp only [CollatzResearch.WordTrace]
  refine ⟨291229253215473375578706227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194152835476982250385804151 291229253215473375578706227)
  ·
    refine ⟨436843879823210063368059341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291229253215473375578706227 436843879823210063368059341)
    ·
      refine ⟨163816454933703773763022253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436843879823210063368059341 163816454933703773763022253)
      ·
        refine ⟨61431170600138915161133345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163816454933703773763022253 61431170600138915161133345)
        ·
          refine ⟨46073377950104186370850009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61431170600138915161133345 46073377950104186370850009)
          ·
            refine ⟨34555033462578139778137507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46073377950104186370850009 34555033462578139778137507)
            ·
              refine ⟨51832550193867209667206261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34555033462578139778137507 51832550193867209667206261)
              ·
                refine ⟨4859301580675050906300587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51832550193867209667206261 4859301580675050906300587)
                ·
                  refine ⟨7288952371012576359450881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859301580675050906300587 7288952371012576359450881)
                  ·
                    refine ⟨5466714278259432269588161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7288952371012576359450881 5466714278259432269588161)
                    ·
                      refine ⟨4100035708694574202191121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466714278259432269588161 4100035708694574202191121)
                      ·
                        rfl

theorem cell23_7984791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7984791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984791 prefixEnd_7984791 := by exact prefixLift 7984791
  have htrace : WordTrace (prefixWord ++ tailWord_7984791) baseStart_7984791 baseEnd_7984791 := by
    simpa [prefixWord, tailWord_7984791, baseEnd_7984791] using wordTrace_append hprefix tailTrace_7984791
  have hstable : (prefixWord ++ tailWord_7984791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984791).length < 2 ^ (prefixWord ++ tailWord_7984791).sum := by decide
  have hdescent : baseEnd_7984791 < baseStart_7984791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984793 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_7984793 : Nat := 118140960795 + 7984793 * 2 ^ 59
def prefixEnd_7984793 : Nat := 4983230072969 + 3 ^ 40 * 7984793 * 2
def baseEnd_7984793 : Nat := 1366678911885294398122037

theorem tailTrace_7984793 : CollatzResearch.WordTrace tailWord_7984793 prefixEnd_7984793 1366678911885294398122037 := by
  unfold tailWord_7984793
  simp only [CollatzResearch.WordTrace]
  refine ⟨291229326161466129920279033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194152884107644086613519355 291229326161466129920279033)
  ·
    refine ⟨218421994621099597440209275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291229326161466129920279033 218421994621099597440209275)
    ·
      refine ⟨327632991931649396160313913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218421994621099597440209275 327632991931649396160313913)
      ·
        refine ⟨245724743948737047120235435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327632991931649396160313913 245724743948737047120235435)
        ·
          refine ⟨368587115923105570680353153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245724743948737047120235435 368587115923105570680353153)
          ·
            refine ⟨276440336942329178010264865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368587115923105570680353153 276440336942329178010264865)
            ·
              refine ⟨207330252706746883507698649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276440336942329178010264865 207330252706746883507698649)
              ·
                refine ⟨155497689530060162630773987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207330252706746883507698649 155497689530060162630773987)
                ·
                  refine ⟨233246534295090243946160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155497689530060162630773987 233246534295090243946160981)
                  ·
                    refine ⟨1366678911885294398122037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 233246534295090243946160981 1366678911885294398122037)
                    ·
                      rfl

theorem cell23_7984793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_7984793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984793 prefixEnd_7984793 := by exact prefixLift 7984793
  have htrace : WordTrace (prefixWord ++ tailWord_7984793) baseStart_7984793 baseEnd_7984793 := by
    simpa [prefixWord, tailWord_7984793, baseEnd_7984793] using wordTrace_append hprefix tailTrace_7984793
  have hstable : (prefixWord ++ tailWord_7984793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984793).length < 2 ^ (prefixWord ++ tailWord_7984793).sum := by decide
  have hdescent : baseEnd_7984793 < baseStart_7984793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984821 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7984821 : Nat := 118140960795 + 7984821 * 2 ^ 59
def prefixEnd_7984821 : Nat := 4983230072969 + 3 ^ 40 * 7984821 * 2
def baseEnd_7984821 : Nat := 4100051113114209084815983

theorem tailTrace_7984821 : CollatzResearch.WordTrace tailWord_7984821 prefixEnd_7984821 4100051113114209084815983 := by
  unfold tailWord_7984821
  simp only [CollatzResearch.WordTrace]
  refine ⟨291230347405364690702298317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194153564936909793801532211 291230347405364690702298317)
  ·
    refine ⟨109211380277011759013361869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291230347405364690702298317 109211380277011759013361869)
    ·
      refine ⟨40954267603879409630010701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109211380277011759013361869 40954267603879409630010701)
      ·
        refine ⟨15357850351454778611254013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40954267603879409630010701 15357850351454778611254013)
        ·
          refine ⟨5759193881795541979220255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15357850351454778611254013 5759193881795541979220255)
          ·
            refine ⟨8638790822693312968830383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759193881795541979220255 8638790822693312968830383)
            ·
              refine ⟨12958186234039969453245575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8638790822693312968830383 12958186234039969453245575)
              ·
                refine ⟨19437279351059954179868363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958186234039969453245575 19437279351059954179868363)
                ·
                  refine ⟨29155919026589931269802545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19437279351059954179868363 29155919026589931269802545)
                  ·
                    refine ⟨21866939269942448452351909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29155919026589931269802545 21866939269942448452351909)
                    ·
                      refine ⟨4100051113114209084815983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21866939269942448452351909 4100051113114209084815983)
                      ·
                        rfl

theorem cell23_7984821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7984821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984821 prefixEnd_7984821 := by exact prefixLift 7984821
  have htrace : WordTrace (prefixWord ++ tailWord_7984821) baseStart_7984821 baseEnd_7984821 := by
    simpa [prefixWord, tailWord_7984821, baseEnd_7984821] using wordTrace_append hprefix tailTrace_7984821
  have hstable : (prefixWord ++ tailWord_7984821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984821).length < 2 ^ (prefixWord ++ tailWord_7984821).sum := by decide
  have hdescent : baseEnd_7984821 < baseStart_7984821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984847 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 4, 2]
def baseStart_7984847 : Nat := 118140960795 + 7984847 * 2 ^ 59
def prefixEnd_7984847 : Nat := 4983230072969 + 3 ^ 40 * 7984847 * 2
def baseEnd_7984847 : Nat := 4100064463611225983090863

theorem tailTrace_7984847 : CollatzResearch.WordTrace tailWord_7984847 prefixEnd_7984847 4100064463611225983090863 := by
  unfold tailWord_7984847
  simp only [CollatzResearch.WordTrace]
  refine ⟨291231295703270497142744795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194154197135513664761829863 291231295703270497142744795)
  ·
    refine ⟨436846943554905745714117193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291231295703270497142744795 436846943554905745714117193)
    ·
      refine ⟨327635207666179309285587895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436846943554905745714117193 327635207666179309285587895)
      ·
        refine ⟨491452811499268963928381843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327635207666179309285587895 491452811499268963928381843)
        ·
          refine ⟨737179217248903445892572765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491452811499268963928381843 737179217248903445892572765)
          ·
            refine ⟨276442206468338792209714787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 737179217248903445892572765 276442206468338792209714787)
            ·
              refine ⟨414663309702508188314572181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276442206468338792209714787 414663309702508188314572181)
              ·
                refine ⟨19437342642305071327245571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414663309702508188314572181 19437342642305071327245571)
                ·
                  refine ⟨29156013963457606990868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19437342642305071327245571 29156013963457606990868357)
                  ·
                    refine ⟨5466752618148301310787817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29156013963457606990868357 5466752618148301310787817)
                    ·
                      refine ⟨4100064463611225983090863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466752618148301310787817 4100064463611225983090863)
                      ·
                        rfl

theorem cell23_7984847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4, 2].length) (baseStart_7984847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984847 prefixEnd_7984847 := by exact prefixLift 7984847
  have htrace : WordTrace (prefixWord ++ tailWord_7984847) baseStart_7984847 baseEnd_7984847 := by
    simpa [prefixWord, tailWord_7984847, baseEnd_7984847] using wordTrace_append hprefix tailTrace_7984847
  have hstable : (prefixWord ++ tailWord_7984847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984847).length < 2 ^ (prefixWord ++ tailWord_7984847).sum := by decide
  have hdescent : baseEnd_7984847 < baseStart_7984847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984864 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2]
def baseStart_7984864 : Nat := 118140960795 + 7984864 * 2 ^ 59
def prefixEnd_7984864 : Nat := 4983230072969 + 3 ^ 40 * 7984864 * 2
def baseEnd_7984864 : Nat := 4100073192782352416578285

theorem tailTrace_7984864 : CollatzResearch.WordTrace tailWord_7984864 prefixEnd_7984864 4100073192782352416578285 := by
  unfold tailWord_7984864
  simp only [CollatzResearch.WordTrace]
  refine ⟨145615957872104454523056823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194154610496139272697409097 145615957872104454523056823)
  ·
    refine ⟨218423936808156681784585235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145615957872104454523056823 218423936808156681784585235)
    ·
      refine ⟨327635905212235022676877853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218423936808156681784585235 327635905212235022676877853)
      ·
        refine ⟨122863464454588133503829195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327635905212235022676877853 122863464454588133503829195)
        ·
          refine ⟨184295196681882200255743793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122863464454588133503829195 184295196681882200255743793)
          ·
            refine ⟨138221397511411650191807845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184295196681882200255743793 138221397511411650191807845)
            ·
              refine ⟨25916512033389684410963971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138221397511411650191807845 25916512033389684410963971)
              ·
                refine ⟨38874768050084526616445957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25916512033389684410963971 38874768050084526616445957)
                ·
                  refine ⟨7289019009390848740583617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38874768050084526616445957 7289019009390848740583617)
                  ·
                    refine ⟨5466764257043136555437713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289019009390848740583617 5466764257043136555437713)
                    ·
                      refine ⟨4100073192782352416578285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466764257043136555437713 4100073192782352416578285)
                      ·
                        rfl

theorem cell23_7984864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_7984864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984864 prefixEnd_7984864 := by exact prefixLift 7984864
  have htrace : WordTrace (prefixWord ++ tailWord_7984864) baseStart_7984864 baseEnd_7984864 := by
    simpa [prefixWord, tailWord_7984864, baseEnd_7984864] using wordTrace_append hprefix tailTrace_7984864
  have hstable : (prefixWord ++ tailWord_7984864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984864).length < 2 ^ (prefixWord ++ tailWord_7984864).sum := by decide
  have hdescent : baseEnd_7984864 < baseStart_7984864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984881 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_7984881 : Nat := 118140960795 + 7984881 * 2 ^ 59
def prefixEnd_7984881 : Nat := 4983230072969 + 3 ^ 40 * 7984881 * 2
def baseEnd_7984881 : Nat := 4100081921953478850065707

theorem tailTrace_7984881 : CollatzResearch.WordTrace tailWord_7984881 prefixEnd_7984881 4100081921953478850065707 := by
  unfold tailWord_7984881
  simp only [CollatzResearch.WordTrace]
  refine ⟨291232535785147320949482497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194155023856764880632988331 291232535785147320949482497)
  ·
    refine ⟨218424401838860490712111873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291232535785147320949482497 218424401838860490712111873)
    ·
      refine ⟨163818301379145368034083905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218424401838860490712111873 163818301379145368034083905)
      ·
        refine ⟨122863726034359026025562929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163818301379145368034083905 122863726034359026025562929)
        ·
          refine ⟨92147794525769269519172197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122863726034359026025562929 92147794525769269519172197)
          ·
            refine ⟨17277711473581738034844787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92147794525769269519172197 17277711473581738034844787)
            ·
              refine ⟨25916567210372607052267181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17277711473581738034844787 25916567210372607052267181)
              ·
                refine ⟨9718712703889727644600193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25916567210372607052267181 9718712703889727644600193)
                ·
                  refine ⟨7289034527917295733450145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718712703889727644600193 7289034527917295733450145)
                  ·
                    refine ⟨5466775895937971800087609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289034527917295733450145 5466775895937971800087609)
                    ·
                      refine ⟨4100081921953478850065707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466775895937971800087609 4100081921953478850065707)
                      ·
                        rfl

theorem cell23_7984881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_7984881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984881 prefixEnd_7984881 := by exact prefixLift 7984881
  have htrace : WordTrace (prefixWord ++ tailWord_7984881) baseStart_7984881 baseEnd_7984881 := by
    simpa [prefixWord, tailWord_7984881, baseEnd_7984881] using wordTrace_append hprefix tailTrace_7984881
  have hstable : (prefixWord ++ tailWord_7984881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984881).length < 2 ^ (prefixWord ++ tailWord_7984881).sum := by decide
  have hdescent : baseEnd_7984881 < baseStart_7984881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984917 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_7984917 : Nat := 118140960795 + 7984917 * 2 ^ 59
def prefixEnd_7984917 : Nat := 4983230072969 + 3 ^ 40 * 7984917 * 2
def baseEnd_7984917 : Nat := 1366700135752346903071847

theorem tailTrace_7984917 : CollatzResearch.WordTrace tailWord_7984917 prefixEnd_7984917 1366700135752346903071847 := by
  unfold tailWord_7984917
  simp only [CollatzResearch.WordTrace]
  refine ⟨291233848813016899097793005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194155899208677932731862003 291233848813016899097793005)
  ·
    refine ⟨109212693304881337161672377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291233848813016899097793005 109212693304881337161672377)
    ·
      refine ⟨81909519978661002871254283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109212693304881337161672377 81909519978661002871254283)
      ·
        refine ⟨122864279967991504306881425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81909519978661002871254283 122864279967991504306881425)
        ·
          refine ⟨92148209975993628230161069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122864279967991504306881425 92148209975993628230161069)
          ·
            refine ⟨34555578740997610586310401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92148209975993628230161069 34555578740997610586310401)
            ·
              refine ⟨25916684055748207939732801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34555578740997610586310401 25916684055748207939732801)
              ·
                refine ⟨19437513041811155954799601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25916684055748207939732801 19437513041811155954799601)
                ·
                  refine ⟨14578134781358366966099701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19437513041811155954799601 14578134781358366966099701)
                  ·
                    refine ⟨1366700135752346903071847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14578134781358366966099701 1366700135752346903071847)
                    ·
                      rfl

theorem cell23_7984917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_7984917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984917 prefixEnd_7984917 := by exact prefixLift 7984917
  have htrace : WordTrace (prefixWord ++ tailWord_7984917) baseStart_7984917 baseEnd_7984917 := by
    simpa [prefixWord, tailWord_7984917, baseEnd_7984917] using wordTrace_append hprefix tailTrace_7984917
  have hstable : (prefixWord ++ tailWord_7984917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984917).length < 2 ^ (prefixWord ++ tailWord_7984917).sum := by decide
  have hdescent : baseEnd_7984917 < baseStart_7984917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984954 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_7984954 : Nat := 118140960795 + 7984954 * 2 ^ 59
def prefixEnd_7984954 : Nat := 4983230072969 + 3 ^ 40 * 7984954 * 2
def baseEnd_7984954 : Nat := 4100119406041257064452871

theorem tailTrace_7984954 : CollatzResearch.WordTrace tailWord_7984954 prefixEnd_7984954 4100119406041257064452871 := by
  unfold tailWord_7984954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72808799578470713604222479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194156798875921902944593277 72808799578470713604222479)
  ·
    refine ⟨109213199367706070406333719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72808799578470713604222479 109213199367706070406333719)
    ·
      refine ⟨163819799051559105609500579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109213199367706070406333719 163819799051559105609500579)
      ·
        refine ⟨245729698577338658414250869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163819799051559105609500579 245729698577338658414250869)
        ·
          refine ⟨23037159241625499226336019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245729698577338658414250869 23037159241625499226336019)
          ·
            refine ⟨34555738862438248839504029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23037159241625499226336019 34555738862438248839504029)
            ·
              refine ⟨12958402073414343314814011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34555738862438248839504029 12958402073414343314814011)
              ·
                refine ⟨19437603110121514972221017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958402073414343314814011 19437603110121514972221017)
                ·
                  refine ⟨14578202332591136229165763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19437603110121514972221017 14578202332591136229165763)
                  ·
                    refine ⟨21867303498886704343748645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14578202332591136229165763 21867303498886704343748645)
                    ·
                      refine ⟨4100119406041257064452871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21867303498886704343748645 4100119406041257064452871)
                      ·
                        rfl

theorem cell23_7984954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_7984954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984954 prefixEnd_7984954 := by exact prefixLift 7984954
  have htrace : WordTrace (prefixWord ++ tailWord_7984954) baseStart_7984954 baseEnd_7984954 := by
    simpa [prefixWord, tailWord_7984954, baseEnd_7984954] using wordTrace_append hprefix tailTrace_7984954
  have hstable : (prefixWord ++ tailWord_7984954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984954).length < 2 ^ (prefixWord ++ tailWord_7984954).sum := by decide
  have hdescent : baseEnd_7984954 < baseStart_7984954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984977 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 8]
def baseStart_7984977 : Nat := 118140960795 + 7984977 * 2 ^ 59
def prefixEnd_7984977 : Nat := 4983230072969 + 3 ^ 40 * 7984977 * 2
def baseEnd_7984977 : Nat := 455570135121812274940585

theorem tailTrace_7984977 : CollatzResearch.WordTrace tailWord_7984977 prefixEnd_7984977 455570135121812274940585 := by
  unfold tailWord_7984977
  simp only [CollatzResearch.WordTrace]
  refine ⟨291236037192799529344977185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194157358128533019563318123 291236037192799529344977185)
  ·
    refine ⟨218427027894599647008732889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291236037192799529344977185 218427027894599647008732889)
    ·
      refine ⟨163820270920949735256549667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218427027894599647008732889 163820270920949735256549667)
      ·
        refine ⟨245730406381424602884824501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163820270920949735256549667 245730406381424602884824501)
        ·
          refine ⟨23037225598258556520452297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245730406381424602884824501 23037225598258556520452297)
          ·
            refine ⟨17277919198693917390339223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23037225598258556520452297 17277919198693917390339223)
            ·
              refine ⟨25916878798040876085508835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17277919198693917390339223 25916878798040876085508835)
              ·
                refine ⟨38875318197061314128263253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25916878798040876085508835 38875318197061314128263253)
                ·
                  refine ⟨455570135121812274940585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38875318197061314128263253 455570135121812274940585)
                  ·
                    rfl

theorem cell23_7984977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_7984977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984977 prefixEnd_7984977 := by exact prefixLift 7984977
  have htrace : WordTrace (prefixWord ++ tailWord_7984977) baseStart_7984977 baseEnd_7984977 := by
    simpa [prefixWord, tailWord_7984977, baseEnd_7984977] using wordTrace_append hprefix tailTrace_7984977
  have hstable : (prefixWord ++ tailWord_7984977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984977).length < 2 ^ (prefixWord ++ tailWord_7984977).sum := by decide
  have hdescent : baseEnd_7984977 < baseStart_7984977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7984981 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7984981 : Nat := 118140960795 + 7984981 * 2 ^ 59
def prefixEnd_7984981 : Nat := 4983230072969 + 3 ^ 40 * 7984981 * 2
def baseEnd_7984981 : Nat := 1366711090006309486271749

theorem tailTrace_7984981 : CollatzResearch.WordTrace tailWord_7984981 prefixEnd_7984981 1366711090006309486271749 := by
  unfold tailWord_7984981
  simp only [CollatzResearch.WordTrace]
  refine ⟨291236183084785038028122797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194157455389856692018748531 291236183084785038028122797)
  ·
    refine ⟨109213568656794389260546049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291236183084785038028122797 109213568656794389260546049)
    ·
      refine ⟨81910176492595791945409537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109213568656794389260546049 81910176492595791945409537)
      ·
        refine ⟨61432632369446843959057153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81910176492595791945409537 61432632369446843959057153)
        ·
          refine ⟨46074474277085132969292865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61432632369446843959057153 46074474277085132969292865)
          ·
            refine ⟨34555855707813849726969649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46074474277085132969292865 34555855707813849726969649)
            ·
              refine ⟨25916891780860387295227237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34555855707813849726969649 25916891780860387295227237)
              ·
                refine ⟨4859417208911322617855107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25916891780860387295227237 4859417208911322617855107)
                ·
                  refine ⟨7289125813366983926782661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859417208911322617855107 7289125813366983926782661)
                  ·
                    refine ⟨1366711090006309486271749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289125813366983926782661 1366711090006309486271749)
                    ·
                      rfl

theorem cell23_7984981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7984981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7984981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7984981 prefixEnd_7984981 := by exact prefixLift 7984981
  have htrace : WordTrace (prefixWord ++ tailWord_7984981) baseStart_7984981 baseEnd_7984981 := by
    simpa [prefixWord, tailWord_7984981, baseEnd_7984981] using wordTrace_append hprefix tailTrace_7984981
  have hstable : (prefixWord ++ tailWord_7984981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7984981).length < 2 ^ (prefixWord ++ tailWord_7984981).sum := by decide
  have hdescent : baseEnd_7984981 < baseStart_7984981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7984981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985058 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_7985058 : Nat := 118140960795 + 7985058 * 2 ^ 59
def prefixEnd_7985058 : Nat := 4983230072969 + 3 ^ 40 * 7985058 * 2
def baseEnd_7985058 : Nat := 1366724269343108219184131

theorem tailTrace_7985058 : CollatzResearch.WordTrace tailWord_7985058 prefixEnd_7985058 1366724269343108219184131 := by
  unfold tailWord_7985058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72809747876376520044668957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194159327670337386785783885 72809747876376520044668957)
  ·
    refine ⟨27303655453641195016750859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72809747876376520044668957 27303655453641195016750859)
    ·
      refine ⟨40955483180461792525126289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27303655453641195016750859 40955483180461792525126289)
      ·
        refine ⟨30716612385346344393844717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40955483180461792525126289 30716612385346344393844717)
        ·
          refine ⟨11518729644504879147691769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30716612385346344393844717 11518729644504879147691769)
          ·
            refine ⟨8639047233378659360768827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11518729644504879147691769 8639047233378659360768827)
            ·
              refine ⟨12958570850067989041153241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639047233378659360768827 12958570850067989041153241)
              ·
                refine ⟨9718928137550991780864931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12958570850067989041153241 9718928137550991780864931)
                ·
                  refine ⟨14578392206326487671297397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9718928137550991780864931 14578392206326487671297397)
                  ·
                    refine ⟨1366724269343108219184131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14578392206326487671297397 1366724269343108219184131)
                    ·
                      rfl

theorem cell23_7985058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_7985058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985058 prefixEnd_7985058 := by exact prefixLift 7985058
  have htrace : WordTrace (prefixWord ++ tailWord_7985058) baseStart_7985058 baseEnd_7985058 := by
    simpa [prefixWord, tailWord_7985058, baseEnd_7985058] using wordTrace_append hprefix tailTrace_7985058
  have hstable : (prefixWord ++ tailWord_7985058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985058).length < 2 ^ (prefixWord ++ tailWord_7985058).sum := by decide
  have hdescent : baseEnd_7985058 < baseStart_7985058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985061 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_7985061 : Nat := 118140960795 + 7985061 * 2 ^ 59
def prefixEnd_7985061 : Nat := 4983230072969 + 3 ^ 40 * 7985061 * 2
def baseEnd_7985061 : Nat := 4100174348471288145814879

theorem tailTrace_7985061 : CollatzResearch.WordTrace tailWord_7985061 prefixEnd_7985061 4100174348471288145814879 := by
  unfold tailWord_7985061
  simp only [CollatzResearch.WordTrace]
  refine ⟨291239100924495211691035037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194159400616330141127356691 291239100924495211691035037)
  ·
    refine ⟨109214662846685704384138139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291239100924495211691035037 109214662846685704384138139)
    ·
      refine ⟨163821994270028556576207209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109214662846685704384138139 163821994270028556576207209)
      ·
        refine ⟨122866495702521417432155407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163821994270028556576207209 122866495702521417432155407)
        ·
          refine ⟨184299743553782126148233111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122866495702521417432155407 184299743553782126148233111)
          ·
            refine ⟨276449615330673189222349667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184299743553782126148233111 276449615330673189222349667)
            ·
              refine ⟨414674422996009783833524501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276449615330673189222349667 414674422996009783833524501)
              ·
                refine ⟨19437863577937958617196461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414674422996009783833524501 19437863577937958617196461)
                ·
                  refine ⟨7289198841726734481448673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19437863577937958617196461 7289198841726734481448673)
                  ·
                    refine ⟨5466899131295050861086505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289198841726734481448673 5466899131295050861086505)
                    ·
                      refine ⟨4100174348471288145814879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466899131295050861086505 4100174348471288145814879)
                      ·
                        rfl

theorem cell23_7985061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_7985061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985061 prefixEnd_7985061 := by exact prefixLift 7985061
  have htrace : WordTrace (prefixWord ++ tailWord_7985061) baseStart_7985061 baseEnd_7985061 := by
    simpa [prefixWord, tailWord_7985061, baseEnd_7985061] using wordTrace_append hprefix tailTrace_7985061
  have hstable : (prefixWord ++ tailWord_7985061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985061).length < 2 ^ (prefixWord ++ tailWord_7985061).sum := by decide
  have hdescent : baseEnd_7985061 < baseStart_7985061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985084 : List Nat := [2, 2, 2, 5, 1, 11]
def baseStart_7985084 : Nat := 118140960795 + 7985084 * 2 ^ 59
def prefixEnd_7985084 : Nat := 4983230072969 + 3 ^ 40 * 7985084 * 2
def baseEnd_7985084 : Nat := 16873194068009636032211

theorem tailTrace_7985084 : CollatzResearch.WordTrace tailWord_7985084 prefixEnd_7985084 16873194068009636032211 := by
  unfold tailWord_7985084
  simp only [CollatzResearch.WordTrace]
  refine ⟨145619969901705943309561153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194159959868941257746081537 145619969901705943309561153)
  ·
    refine ⟨109214977426279457482170865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145619969901705943309561153 109214977426279457482170865)
    ·
      refine ⟨81911233069709593111628149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109214977426279457482170865 81911233069709593111628149)
      ·
        refine ⟨7679178100285274354215139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81911233069709593111628149 7679178100285274354215139)
        ·
          refine ⟨11518767150427911531322709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7679178100285274354215139 11518767150427911531322709)
          ·
            refine ⟨16873194068009636032211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11518767150427911531322709 16873194068009636032211)
            ·
              rfl

theorem cell23_7985084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 11].length) (baseStart_7985084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985084 prefixEnd_7985084 := by exact prefixLift 7985084
  have htrace : WordTrace (prefixWord ++ tailWord_7985084) baseStart_7985084 baseEnd_7985084 := by
    simpa [prefixWord, tailWord_7985084, baseEnd_7985084] using wordTrace_append hprefix tailTrace_7985084
  have hstable : (prefixWord ++ tailWord_7985084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985084).length < 2 ^ (prefixWord ++ tailWord_7985084).sum := by decide
  have hdescent : baseEnd_7985084 < baseStart_7985084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985111 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_7985111 : Nat := 118140960795 + 7985111 * 2 ^ 59
def prefixEnd_7985111 : Nat := 4983230072969 + 3 ^ 40 * 7985111 * 2
def baseEnd_7985111 : Nat := 4100200022504012950189649

theorem tailTrace_7985111 : CollatzResearch.WordTrace tailWord_7985111 prefixEnd_7985111 4100200022504012950189649 := by
  unfold tailWord_7985111
  simp only [CollatzResearch.WordTrace]
  refine ⟨291240924574314070230355187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194160616382876046820236791 291240924574314070230355187)
  ·
    refine ⟨436861386861471105345532781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291240924574314070230355187 436861386861471105345532781)
    ·
      refine ⟨163823020073051664504574793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436861386861471105345532781 163823020073051664504574793)
      ·
        refine ⟨122867265054788748378431095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163823020073051664504574793 122867265054788748378431095)
        ·
          refine ⟨184300897582183122567646643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122867265054788748378431095 184300897582183122567646643)
          ·
            refine ⟨276451346373274683851469965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184300897582183122567646643 276451346373274683851469965)
            ·
              refine ⟨103669254889978006444301237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276451346373274683851469965 103669254889978006444301237)
              ·
                refine ⟨9718992645935438104153241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103669254889978006444301237 9718992645935438104153241)
                ·
                  refine ⟨7289244484451578578114931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718992645935438104153241 7289244484451578578114931)
                  ·
                    refine ⟨10933866726677367867172397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289244484451578578114931 10933866726677367867172397)
                    ·
                      refine ⟨4100200022504012950189649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10933866726677367867172397 4100200022504012950189649)
                      ·
                        rfl

theorem cell23_7985111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_7985111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985111 prefixEnd_7985111 := by exact prefixLift 7985111
  have htrace : WordTrace (prefixWord ++ tailWord_7985111) baseStart_7985111 baseEnd_7985111 := by
    simpa [prefixWord, tailWord_7985111, baseEnd_7985111] using wordTrace_append hprefix tailTrace_7985111
  have hstable : (prefixWord ++ tailWord_7985111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985111).length < 2 ^ (prefixWord ++ tailWord_7985111).sum := by decide
  have hdescent : baseEnd_7985111 < baseStart_7985111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985121 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7985121 : Nat := 118140960795 + 7985121 * 2 ^ 59
def prefixEnd_7985121 : Nat := 4983230072969 + 3 ^ 40 * 7985121 * 2
def baseEnd_7985121 : Nat := 4100205157310557911064603

theorem tailTrace_7985121 : CollatzResearch.WordTrace tailWord_7985121 prefixEnd_7985121 4100205157310557911064603 := by
  unfold tailWord_7985121
  simp only [CollatzResearch.WordTrace]
  refine ⟨291241289304277841938219217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194160859536185227958812811 291241289304277841938219217)
  ·
    refine ⟨218430966978208381453664413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291241289304277841938219217 218430966978208381453664413)
    ·
      refine ⟨81911612616828143045124155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218430966978208381453664413 81911612616828143045124155)
      ·
        refine ⟨122867418925242214567686233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81911612616828143045124155 122867418925242214567686233)
        ·
          refine ⟨92150564193931660925764675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122867418925242214567686233 92150564193931660925764675)
          ·
            refine ⟨138225846290897491388647013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92150564193931660925764675 138225846290897491388647013)
            ·
              refine ⟨25917346179543279635371315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138225846290897491388647013 25917346179543279635371315)
              ·
                refine ⟨38876019269314919453056973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25917346179543279635371315 38876019269314919453056973)
                ·
                  refine ⟨14578507225993094794896365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38876019269314919453056973 14578507225993094794896365)
                  ·
                    refine ⟨5466940209747410548086137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14578507225993094794896365 5466940209747410548086137)
                    ·
                      refine ⟨4100205157310557911064603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5466940209747410548086137 4100205157310557911064603)
                      ·
                        rfl

theorem cell23_7985121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7985121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985121 prefixEnd_7985121 := by exact prefixLift 7985121
  have htrace : WordTrace (prefixWord ++ tailWord_7985121) baseStart_7985121 baseEnd_7985121 := by
    simpa [prefixWord, tailWord_7985121, baseEnd_7985121] using wordTrace_append hprefix tailTrace_7985121
  have hstable : (prefixWord ++ tailWord_7985121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985121).length < 2 ^ (prefixWord ++ tailWord_7985121).sum := by decide
  have hdescent : baseEnd_7985121 < baseStart_7985121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985164 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_7985164 : Nat := 118140960795 + 7985164 * 2 ^ 59
def prefixEnd_7985164 : Nat := 4983230072969 + 3 ^ 40 * 7985164 * 2
def baseEnd_7985164 : Nat := 4100227236978701242826905

theorem tailTrace_7985164 : CollatzResearch.WordTrace tailWord_7985164 prefixEnd_7985164 4100227236978701242826905 := by
  unfold tailWord_7985164
  simp only [CollatzResearch.WordTrace]
  refine ⟨145621428821561030141017273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194161905095414706854689697 145621428821561030141017273)
  ·
    refine ⟨109216071616170772605762955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145621428821561030141017273 109216071616170772605762955)
    ·
      refine ⟨163824107424256158908644433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109216071616170772605762955 163824107424256158908644433)
      ·
        refine ⟨122868080568192119181483325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163824107424256158908644433 122868080568192119181483325)
        ·
          refine ⟨46075530213072044693056247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122868080568192119181483325 46075530213072044693056247)
          ·
            refine ⟨69113295319608067039584371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46075530213072044693056247 69113295319608067039584371)
            ·
              refine ⟨103669942979412100559376557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69113295319608067039584371 103669942979412100559376557)
              ·
                refine ⟨38876228617279537709766209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103669942979412100559376557 38876228617279537709766209)
                ·
                  refine ⟨29157171462959653282324657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38876228617279537709766209 29157171462959653282324657)
                  ·
                    refine ⟨21867878597219739961743493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29157171462959653282324657 21867878597219739961743493)
                    ·
                      refine ⟨4100227236978701242826905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21867878597219739961743493 4100227236978701242826905)
                      ·
                        rfl

theorem cell23_7985164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_7985164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985164 prefixEnd_7985164 := by exact prefixLift 7985164
  have htrace : WordTrace (prefixWord ++ tailWord_7985164) baseStart_7985164 baseEnd_7985164 := by
    simpa [prefixWord, tailWord_7985164, baseEnd_7985164] using wordTrace_append hprefix tailTrace_7985164
  have hstable : (prefixWord ++ tailWord_7985164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985164).length < 2 ^ (prefixWord ++ tailWord_7985164).sum := by decide
  have hdescent : baseEnd_7985164 < baseStart_7985164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985208 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 7]
def baseStart_7985208 : Nat := 118140960795 + 7985208 * 2 ^ 59
def prefixEnd_7985208 : Nat := 4983230072969 + 3 ^ 40 * 7985208 * 2
def baseEnd_7985208 : Nat := 455583314458611007852967

theorem tailTrace_7985208 : CollatzResearch.WordTrace tailWord_7985208 prefixEnd_7985208 455583314458611007852967 := by
  unfold tailWord_7985208
  simp only [CollatzResearch.WordTrace]
  refine ⟨145622231227481327898318139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194162974969975103864424185 145622231227481327898318139)
  ·
    refine ⟨218433346841221991847477209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145622231227481327898318139 218433346841221991847477209)
    ·
      refine ⟨163825010130916493885607907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218433346841221991847477209 163825010130916493885607907)
      ·
        refine ⟨245737515196374740828411861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163825010130916493885607907 245737515196374740828411861)
        ·
          refine ⟨5759473012415032988165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 245737515196374740828411861 5759473012415032988165903)
          ·
            refine ⟨8639209518622549482248855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759473012415032988165903 8639209518622549482248855)
            ·
              refine ⟨12958814277933824223373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639209518622549482248855 12958814277933824223373283)
              ·
                refine ⟨19438221416900736335059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958814277933824223373283 19438221416900736335059925)
                ·
                  refine ⟨455583314458611007852967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19438221416900736335059925 455583314458611007852967)
                  ·
                    rfl

theorem cell23_7985208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_7985208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985208 prefixEnd_7985208 := by exact prefixLift 7985208
  have htrace : WordTrace (prefixWord ++ tailWord_7985208) baseStart_7985208 baseEnd_7985208 := by
    simpa [prefixWord, tailWord_7985208, baseEnd_7985208] using wordTrace_append hprefix tailTrace_7985208
  have hstable : (prefixWord ++ tailWord_7985208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985208).length < 2 ^ (prefixWord ++ tailWord_7985208).sum := by decide
  have hdescent : baseEnd_7985208 < baseStart_7985208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985224 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_7985224 : Nat := 118140960795 + 7985224 * 2 ^ 59
def prefixEnd_7985224 : Nat := 4983230072969 + 3 ^ 40 * 7985224 * 2
def baseEnd_7985224 : Nat := 4100258045817971008076629

theorem tailTrace_7985224 : CollatzResearch.WordTrace tailWord_7985224 prefixEnd_7985224 4100258045817971008076629 := by
  unfold tailWord_7985224
  simp only [CollatzResearch.WordTrace]
  refine ⟨145622523011452345264609363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194163364015269793686145817 145622523011452345264609363)
  ·
    refine ⟨218433784517178517896914045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145622523011452345264609363 218433784517178517896914045)
    ·
      refine ⟨81912669193941944211342767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218433784517178517896914045 81912669193941944211342767)
      ·
        refine ⟨122869003790912916317014151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81912669193941944211342767 122869003790912916317014151)
        ·
          refine ⟨184303505686369374475521227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122869003790912916317014151 184303505686369374475521227)
          ·
            refine ⟨276455258529554061713281841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184303505686369374475521227 276455258529554061713281841)
            ·
              refine ⟨207341443897165546284961381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276455258529554061713281841 207341443897165546284961381)
              ·
                refine ⟨38876520730718539928430259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207341443897165546284961381 38876520730718539928430259)
                ·
                  refine ⟨58314781096077809892645389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38876520730718539928430259 58314781096077809892645389)
                  ·
                    refine ⟨21868042911029178709742021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58314781096077809892645389 21868042911029178709742021)
                    ·
                      refine ⟨4100258045817971008076629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21868042911029178709742021 4100258045817971008076629)
                      ·
                        rfl

theorem cell23_7985224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_7985224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985224 prefixEnd_7985224 := by exact prefixLift 7985224
  have htrace : WordTrace (prefixWord ++ tailWord_7985224) baseStart_7985224 baseEnd_7985224 := by
    simpa [prefixWord, tailWord_7985224, baseEnd_7985224] using wordTrace_append hprefix tailTrace_7985224
  have hstable : (prefixWord ++ tailWord_7985224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985224).length < 2 ^ (prefixWord ++ tailWord_7985224).sum := by decide
  have hdescent : baseEnd_7985224 < baseStart_7985224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985241 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_7985241 : Nat := 118140960795 + 7985241 * 2 ^ 59
def prefixEnd_7985241 : Nat := 4983230072969 + 3 ^ 40 * 7985241 * 2
def baseEnd_7985241 : Nat := 4100266774989097441564051

theorem tailTrace_7985241 : CollatzResearch.WordTrace tailWord_7985241 prefixEnd_7985241 4100266774989097441564051 := by
  unfold tailWord_7985241
  simp only [CollatzResearch.WordTrace]
  refine ⟨291245666063843102432587577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194163777375895401621725051 291245666063843102432587577)
  ·
    refine ⟨218434249547882326824440683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291245666063843102432587577 218434249547882326824440683)
    ·
      refine ⟨327651374321823490236661025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218434249547882326824440683 327651374321823490236661025)
      ·
        refine ⟨245738530741367617677495769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327651374321823490236661025 245738530741367617677495769)
        ·
          refine ⟨184303898056025713258121827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245738530741367617677495769 184303898056025713258121827)
          ·
            refine ⟨276455847084038569887182741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184303898056025713258121827 276455847084038569887182741)
            ·
              refine ⟨12958867832064307963461691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276455847084038569887182741 12958867832064307963461691)
              ·
                refine ⟨19438301748096461945192537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958867832064307963461691 19438301748096461945192537)
                ·
                  refine ⟨14578726311072346458894403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19438301748096461945192537 14578726311072346458894403)
                  ·
                    refine ⟨21868089466608519688341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14578726311072346458894403 21868089466608519688341605)
                    ·
                      refine ⟨4100266774989097441564051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21868089466608519688341605 4100266774989097441564051)
                      ·
                        rfl

theorem cell23_7985241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_7985241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985241 prefixEnd_7985241 := by exact prefixLift 7985241
  have htrace : WordTrace (prefixWord ++ tailWord_7985241) baseStart_7985241 baseEnd_7985241 := by
    simpa [prefixWord, tailWord_7985241, baseEnd_7985241] using wordTrace_append hprefix tailTrace_7985241
  have hstable : (prefixWord ++ tailWord_7985241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985241).length < 2 ^ (prefixWord ++ tailWord_7985241).sum := by decide
  have hdescent : baseEnd_7985241 < baseStart_7985241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985308 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7985308 : Nat := 118140960795 + 7985308 * 2 ^ 59
def prefixEnd_7985308 : Nat := 4983230072969 + 3 ^ 40 * 7985308 * 2
def baseEnd_7985308 : Nat := 4100301178192948679426243

theorem tailTrace_7985308 : CollatzResearch.WordTrace tailWord_7985308 prefixEnd_7985308 4100301178192948679426243 := by
  unfold tailWord_7985308
  simp only [CollatzResearch.WordTrace]
  refine ⟨145624054877300186437638289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194165406503066915250184385 145624054877300186437638289)
  ·
    refine ⟨109218041157975139828228717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145624054877300186437638289 109218041157975139828228717)
    ·
      refine ⟨40956765434240677435585769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109218041157975139828228717 40956765434240677435585769)
      ·
        refine ⟨30717574075680508076689327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40956765434240677435585769 30717574075680508076689327)
        ·
          refine ⟨46076361113520762115033991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30717574075680508076689327 46076361113520762115033991)
          ·
            refine ⟨69114541670281143172550987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46076361113520762115033991 69114541670281143172550987)
            ·
              refine ⟨103671812505421714758826481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69114541670281143172550987 103671812505421714758826481)
              ·
                refine ⟨77753859379066286069119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103671812505421714758826481 77753859379066286069119861)
                ·
                  refine ⟨7289424316787464318979987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77753859379066286069119861 7289424316787464318979987)
                  ·
                    refine ⟨10934136475181196478469981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289424316787464318979987 10934136475181196478469981)
                    ·
                      refine ⟨4100301178192948679426243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934136475181196478469981 4100301178192948679426243)
                      ·
                        rfl

theorem cell23_7985308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7985308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985308 prefixEnd_7985308 := by exact prefixLift 7985308
  have htrace : WordTrace (prefixWord ++ tailWord_7985308) baseStart_7985308 baseEnd_7985308 := by
    simpa [prefixWord, tailWord_7985308, baseEnd_7985308] using wordTrace_append hprefix tailTrace_7985308
  have hstable : (prefixWord ++ tailWord_7985308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985308).length < 2 ^ (prefixWord ++ tailWord_7985308).sum := by decide
  have hdescent : baseEnd_7985308 < baseStart_7985308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985325 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_7985325 : Nat := 118140960795 + 7985325 * 2 ^ 59
def prefixEnd_7985325 : Nat := 4983230072969 + 3 ^ 40 * 7985325 * 2
def baseEnd_7985325 : Nat := 4100309907364075112913665

theorem tailTrace_7985325 : CollatzResearch.WordTrace tailWord_7985325 prefixEnd_7985325 4100309907364075112913665 := by
  unfold tailWord_7985325
  simp only [CollatzResearch.WordTrace]
  refine ⟨291248729795538784778645429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194165819863692523185763619 291248729795538784778645429)
  ·
    refine ⟨27304568418331761072998009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291248729795538784778645429 27304568418331761072998009)
    ·
      refine ⟨20478426313748820804748507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27304568418331761072998009 20478426313748820804748507)
      ·
        refine ⟨30717639470623231207122761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20478426313748820804748507 30717639470623231207122761)
        ·
          refine ⟨23038229602967423405342071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30717639470623231207122761 23038229602967423405342071)
          ·
            refine ⟨34557344404451135108013107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23038229602967423405342071 34557344404451135108013107)
            ·
              refine ⟨51836016606676702662019661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34557344404451135108013107 51836016606676702662019661)
              ·
                refine ⟨19438506227503763498257373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51836016606676702662019661 19438506227503763498257373)
                ·
                  refine ⟨7289439835313911311846515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19438506227503763498257373 7289439835313911311846515)
                  ·
                    refine ⟨10934159752970866967769773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289439835313911311846515 10934159752970866967769773)
                    ·
                      refine ⟨4100309907364075112913665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934159752970866967769773 4100309907364075112913665)
                      ·
                        rfl

theorem cell23_7985325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_7985325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985325 prefixEnd_7985325 := by exact prefixLift 7985325
  have htrace : WordTrace (prefixWord ++ tailWord_7985325) baseStart_7985325 baseEnd_7985325 := by
    simpa [prefixWord, tailWord_7985325, baseEnd_7985325] using wordTrace_append hprefix tailTrace_7985325
  have hstable : (prefixWord ++ tailWord_7985325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985325).length < 2 ^ (prefixWord ++ tailWord_7985325).sum := by decide
  have hdescent : baseEnd_7985325 < baseStart_7985325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985358 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_7985358 : Nat := 118140960795 + 7985358 * 2 ^ 59
def prefixEnd_7985358 : Nat := 4983230072969 + 3 ^ 40 * 7985358 * 2
def baseEnd_7985358 : Nat := 1366775617408557827933671

theorem tailTrace_7985358 : CollatzResearch.WordTrace tailWord_7985358 prefixEnd_7985358 1366775617408557827933671 := by
  unfold tailWord_7985358
  simp only [CollatzResearch.WordTrace]
  refine ⟨36406241675552403926824591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194166622269612820943064485 36406241675552403926824591)
  ·
    refine ⟨54609362513328605890236887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36406241675552403926824591 54609362513328605890236887)
    ·
      refine ⟨81914043769992908835355331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54609362513328605890236887 81914043769992908835355331)
      ·
        refine ⟨122871065654989363253032997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81914043769992908835355331 122871065654989363253032997)
        ·
          refine ⟨23038324810310505609943687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122871065654989363253032997 23038324810310505609943687)
          ·
            refine ⟨34557487215465758414915531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23038324810310505609943687 34557487215465758414915531)
            ·
              refine ⟨51836230823198637622373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34557487215465758414915531 51836230823198637622373297)
              ·
                refine ⟨38877173117398978216779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51836230823198637622373297 38877173117398978216779973)
                ·
                  refine ⟨7289469959512308415646245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38877173117398978216779973 7289469959512308415646245)
                  ·
                    refine ⟨1366775617408557827933671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289469959512308415646245 1366775617408557827933671)
                    ·
                      rfl

theorem cell23_7985358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_7985358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985358 prefixEnd_7985358 := by exact prefixLift 7985358
  have htrace : WordTrace (prefixWord ++ tailWord_7985358) baseStart_7985358 baseEnd_7985358 := by
    simpa [prefixWord, tailWord_7985358, baseEnd_7985358] using wordTrace_append hprefix tailTrace_7985358
  have hstable : (prefixWord ++ tailWord_7985358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985358).length < 2 ^ (prefixWord ++ tailWord_7985358).sum := by decide
  have hdescent : baseEnd_7985358 < baseStart_7985358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985361 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_7985361 : Nat := 118140960795 + 7985361 * 2 ^ 59
def prefixEnd_7985361 : Nat := 4983230072969 + 3 ^ 40 * 7985361 * 2
def baseEnd_7985361 : Nat := 4100328392667636972063499

theorem tailTrace_7985361 : CollatzResearch.WordTrace tailWord_7985361 prefixEnd_7985361 4100328392667636972063499 := by
  unfold tailWord_7985361
  simp only [CollatzResearch.WordTrace]
  refine ⟨291250042823408362926955937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194166695215605575284637291 291250042823408362926955937)
  ·
    refine ⟨218437532117556272195216953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291250042823408362926955937 218437532117556272195216953)
    ·
      refine ⟨163828149088167204146412715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218437532117556272195216953 163828149088167204146412715)
      ·
        refine ⟨245742223632250806219619073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163828149088167204146412715 245742223632250806219619073)
        ·
          refine ⟨184306667724188104664714305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245742223632250806219619073 184306667724188104664714305)
          ·
            refine ⟨138230000793141078498535729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184306667724188104664714305 138230000793141078498535729)
            ·
              refine ⟨103672500594855808873901797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138230000793141078498535729 103672500594855808873901797)
              ·
                refine ⟨19438593861535464163856587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103672500594855808873901797 19438593861535464163856587)
                ·
                  refine ⟨29157890792303196245784881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19438593861535464163856587 29157890792303196245784881)
                  ·
                    refine ⟨21868418094227397184338661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29157890792303196245784881 21868418094227397184338661)
                    ·
                      refine ⟨4100328392667636972063499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21868418094227397184338661 4100328392667636972063499)
                      ·
                        rfl

theorem cell23_7985361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_7985361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985361 prefixEnd_7985361 := by exact prefixLift 7985361
  have htrace : WordTrace (prefixWord ++ tailWord_7985361) baseStart_7985361 baseEnd_7985361 := by
    simpa [prefixWord, tailWord_7985361, baseEnd_7985361] using wordTrace_append hprefix tailTrace_7985361
  have hstable : (prefixWord ++ tailWord_7985361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985361).length < 2 ^ (prefixWord ++ tailWord_7985361).sum := by decide
  have hdescent : baseEnd_7985361 < baseStart_7985361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985368 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_7985368 : Nat := 118140960795 + 7985368 * 2 ^ 59
def prefixEnd_7985368 : Nat := 4983230072969 + 3 ^ 40 * 7985368 * 2
def baseEnd_7985368 : Nat := 4100331987032218444675967

theorem tailTrace_7985368 : CollatzResearch.WordTrace tailWord_7985368 prefixEnd_7985368 4100331987032218444675967 := by
  unfold tailWord_7985368
  simp only [CollatzResearch.WordTrace]
  refine ⟨145625149067191501561230379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194166865422922002081640505 145625149067191501561230379)
  ·
    refine ⟨218437723600787252341845569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145625149067191501561230379 218437723600787252341845569)
    ·
      refine ⟨163828292700590439256384177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218437723600787252341845569 163828292700590439256384177)
      ·
        refine ⟨122871219525442829442288133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163828292700590439256384177 122871219525442829442288133)
        ·
          refine ⟨23038353661020530520429025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122871219525442829442288133 23038353661020530520429025)
          ·
            refine ⟨17278765245765397890321769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23038353661020530520429025 17278765245765397890321769)
            ·
              refine ⟨12959073934324048417741327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17278765245765397890321769 12959073934324048417741327)
              ·
                refine ⟨19438610901486072626611991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12959073934324048417741327 19438610901486072626611991)
                ·
                  refine ⟨29157916352229108939917987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19438610901486072626611991 29157916352229108939917987)
                  ·
                    refine ⟨43736874528343663409876981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29157916352229108939917987 43736874528343663409876981)
                    ·
                      refine ⟨4100331987032218444675967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43736874528343663409876981 4100331987032218444675967)
                      ·
                        rfl

theorem cell23_7985368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_7985368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985368 prefixEnd_7985368 := by exact prefixLift 7985368
  have htrace : WordTrace (prefixWord ++ tailWord_7985368) baseStart_7985368 baseEnd_7985368 := by
    simpa [prefixWord, tailWord_7985368, baseEnd_7985368] using wordTrace_append hprefix tailTrace_7985368
  have hstable : (prefixWord ++ tailWord_7985368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985368).length < 2 ^ (prefixWord ++ tailWord_7985368).sum := by decide
  have hdescent : baseEnd_7985368 < baseStart_7985368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985441 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7985441 : Nat := 118140960795 + 7985441 * 2 ^ 59
def prefixEnd_7985441 : Nat := 4983230072969 + 3 ^ 40 * 7985441 * 2
def baseEnd_7985441 : Nat := 4100369471119996659063131

theorem tailTrace_7985441 : CollatzResearch.WordTrace tailWord_7985441 prefixEnd_7985441 4100369471119996659063131 := by
  unfold tailWord_7985441
  simp only [CollatzResearch.WordTrace]
  refine ⟨291252960663118536589868177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194168640442079024393245451 291252960663118536589868177)
  ·
    refine ⟨218439720497338902442401133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291252960663118536589868177 218439720497338902442401133)
    ·
      refine ⟨81914895186502088415900425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218439720497338902442401133 81914895186502088415900425)
      ·
        refine ⟨61436171389876566311925319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81914895186502088415900425 61436171389876566311925319)
        ·
          refine ⟨92154257084814849467887979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61436171389876566311925319 92154257084814849467887979)
          ·
            refine ⟨138231385627222274201831969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92154257084814849467887979 138231385627222274201831969)
            ·
              refine ⟨103673539220416705651373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138231385627222274201831969 103673539220416705651373977)
              ·
                refine ⟨77755154415312529238530483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103673539220416705651373977 77755154415312529238530483)
                ·
                  refine ⟨116632731622968793857795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77755154415312529238530483 116632731622968793857795725)
                  ·
                    refine ⟨43737274358613297696673397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116632731622968793857795725 43737274358613297696673397)
                    ·
                      refine ⟨4100369471119996659063131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43737274358613297696673397 4100369471119996659063131)
                      ·
                        rfl

theorem cell23_7985441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7985441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985441 prefixEnd_7985441 := by exact prefixLift 7985441
  have htrace : WordTrace (prefixWord ++ tailWord_7985441) baseStart_7985441 baseEnd_7985441 := by
    simpa [prefixWord, tailWord_7985441, baseEnd_7985441] using wordTrace_append hprefix tailTrace_7985441
  have hstable : (prefixWord ++ tailWord_7985441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985441).length < 2 ^ (prefixWord ++ tailWord_7985441).sum := by decide
  have hdescent : baseEnd_7985441 < baseStart_7985441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985488 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_7985488 : Nat := 118140960795 + 7985488 * 2 ^ 59
def prefixEnd_7985488 : Nat := 4983230072969 + 3 ^ 40 * 7985488 * 2
def baseEnd_7985488 : Nat := 4100393604710757975175415

theorem tailTrace_7985488 : CollatzResearch.WordTrace tailWord_7985488 prefixEnd_7985488 4100393604710757975175415 := by
  unfold tailWord_7985488
  simp only [CollatzResearch.WordTrace]
  refine ⟨145627337446974131808414559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194169783262632175744552745 145627337446974131808414559)
  ·
    refine ⟨218441006170461197712621839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145627337446974131808414559 218441006170461197712621839)
    ·
      refine ⟨327661509255691796568932759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218441006170461197712621839 327661509255691796568932759)
      ·
        refine ⟨491492263883537694853399139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327661509255691796568932759 491492263883537694853399139)
        ·
          refine ⟨737238395825306542280098709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491492263883537694853399139 737238395825306542280098709)
          ·
            refine ⟨34558049804311244169379627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 737238395825306542280098709 34558049804311244169379627)
            ·
              refine ⟨51837074706466866254069441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34558049804311244169379627 51837074706466866254069441)
              ·
                refine ⟨38877806029850149690552081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51837074706466866254069441 38877806029850149690552081)
                ·
                  refine ⟨29158354522387612267914061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38877806029850149690552081 29158354522387612267914061)
                  ·
                    refine ⟨10934382945895354600467773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29158354522387612267914061 10934382945895354600467773)
                    ·
                      refine ⟨4100393604710757975175415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934382945895354600467773 4100393604710757975175415)
                      ·
                        rfl

theorem cell23_7985488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_7985488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985488 prefixEnd_7985488 := by exact prefixLift 7985488
  have htrace : WordTrace (prefixWord ++ tailWord_7985488) baseStart_7985488 baseEnd_7985488 := by
    simpa [prefixWord, tailWord_7985488, baseEnd_7985488] using wordTrace_append hprefix tailTrace_7985488
  have hstable : (prefixWord ++ tailWord_7985488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985488).length < 2 ^ (prefixWord ++ tailWord_7985488).sum := by decide
  have hdescent : baseEnd_7985488 < baseStart_7985488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985489 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_7985489 : Nat := 118140960795 + 7985489 * 2 ^ 59
def prefixEnd_7985489 : Nat := 4983230072969 + 3 ^ 40 * 7985489 * 2
def baseEnd_7985489 : Nat := 4100394118191412471262911

theorem tailTrace_7985489 : CollatzResearch.WordTrace tailWord_7985489 prefixEnd_7985489 4100394118191412471262911 := by
  unfold tailWord_7985489
  simp only [CollatzResearch.WordTrace]
  refine ⟨291254711366944640787615521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194169807577963093858410347 291254711366944640787615521)
  ·
    refine ⟨218441033525208480590711641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291254711366944640787615521 218441033525208480590711641)
    ·
      refine ⟨163830775143906360443033731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218441033525208480590711641 163830775143906360443033731)
      ·
        refine ⟨245746162715859540664550597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163830775143906360443033731 245746162715859540664550597)
        ·
          refine ⟨46077405509223663874603237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245746162715859540664550597 46077405509223663874603237)
          ·
            refine ⟨8639513532979436976488107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46077405509223663874603237 8639513532979436976488107)
            ·
              refine ⟨12959270299469155464732161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639513532979436976488107 12959270299469155464732161)
              ·
                refine ⟨9719452724601866598549121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12959270299469155464732161 9719452724601866598549121)
                ·
                  refine ⟨7289589543451399948911841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9719452724601866598549121 7289589543451399948911841)
                  ·
                    refine ⟨5467192157588549961683881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289589543451399948911841 5467192157588549961683881)
                    ·
                      refine ⟨4100394118191412471262911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467192157588549961683881 4100394118191412471262911)
                      ·
                        rfl

theorem cell23_7985489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_7985489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985489 prefixEnd_7985489 := by exact prefixLift 7985489
  have htrace : WordTrace (prefixWord ++ tailWord_7985489) baseStart_7985489 baseEnd_7985489 := by
    simpa [prefixWord, tailWord_7985489, baseEnd_7985489] using wordTrace_append hprefix tailTrace_7985489
  have hstable : (prefixWord ++ tailWord_7985489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985489).length < 2 ^ (prefixWord ++ tailWord_7985489).sum := by decide
  have hdescent : baseEnd_7985489 < baseStart_7985489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985506 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7985506 : Nat := 118140960795 + 7985506 * 2 ^ 59
def prefixEnd_7985506 : Nat := 4983230072969 + 3 ^ 40 * 7985506 * 2
def baseEnd_7985506 : Nat := 4100402847362538904750333

theorem tailTrace_7985506 : CollatzResearch.WordTrace tailWord_7985506 prefixEnd_7985506 4100402847362538904750333 := by
  unfold tailWord_7985506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72813832851970763172746093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194170220938588701793989581 72813832851970763172746093)
  ·
    refine ⟨27305187319489036189779785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72813832851970763172746093 27305187319489036189779785)
    ·
      refine ⟨20478890489616777142334839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27305187319489036189779785 20478890489616777142334839)
      ·
        refine ⟨30718335734425165713502259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20478890489616777142334839 30718335734425165713502259)
        ·
          refine ⟨46077503601637748570253389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30718335734425165713502259 46077503601637748570253389)
          ·
            refine ⟨17279063850614155713845021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46077503601637748570253389 17279063850614155713845021)
            ·
              refine ⟨6479648943980308392691883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17279063850614155713845021 6479648943980308392691883)
              ·
                refine ⟨9719473415970462589037825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479648943980308392691883 9719473415970462589037825)
                ·
                  refine ⟨7289605061977846941778369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9719473415970462589037825 7289605061977846941778369)
                  ·
                    refine ⟨5467203796483385206333777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7289605061977846941778369 5467203796483385206333777)
                    ·
                      refine ⟨4100402847362538904750333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467203796483385206333777 4100402847362538904750333)
                      ·
                        rfl

theorem cell23_7985506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7985506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985506 prefixEnd_7985506 := by exact prefixLift 7985506
  have htrace : WordTrace (prefixWord ++ tailWord_7985506) baseStart_7985506 baseEnd_7985506 := by
    simpa [prefixWord, tailWord_7985506, baseEnd_7985506] using wordTrace_append hprefix tailTrace_7985506
  have hstable : (prefixWord ++ tailWord_7985506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985506).length < 2 ^ (prefixWord ++ tailWord_7985506).sum := by decide
  have hdescent : baseEnd_7985506 < baseStart_7985506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985521 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_7985521 : Nat := 118140960795 + 7985521 * 2 ^ 59
def prefixEnd_7985521 : Nat := 4983230072969 + 3 ^ 40 * 7985521 * 2
def baseEnd_7985521 : Nat := 1366803516524118782020921

theorem tailTrace_7985521 : CollatzResearch.WordTrace tailWord_7985521 prefixEnd_7985521 1366803516524118782020921 := by
  unfold tailWord_7985521
  simp only [CollatzResearch.WordTrace]
  refine ⟨291255878502828710252780417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194170585668552473501853611 291255878502828710252780417)
  ·
    refine ⟨218441908877121532689585313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291255878502828710252780417 218441908877121532689585313)
    ·
      refine ⟨163831431657841149517188985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218441908877121532689585313 163831431657841149517188985)
      ·
        refine ⟨122873573743380862137891739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163831431657841149517188985 122873573743380862137891739)
        ·
          refine ⟨184310360615071293206837609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122873573743380862137891739 184310360615071293206837609)
          ·
            refine ⟨138232770461303469905128207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184310360615071293206837609 138232770461303469905128207)
            ·
              refine ⟨207349155691955204857692311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138232770461303469905128207 207349155691955204857692311)
              ·
                refine ⟨311023733537932807286538467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207349155691955204857692311 311023733537932807286538467)
                ·
                  refine ⟨466535600306899210929807701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311023733537932807286538467 466535600306899210929807701)
                  ·
                    refine ⟨1366803516524118782020921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 466535600306899210929807701 1366803516524118782020921)
                    ·
                      rfl

theorem cell23_7985521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_7985521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985521 prefixEnd_7985521 := by exact prefixLift 7985521
  have htrace : WordTrace (prefixWord ++ tailWord_7985521) baseStart_7985521 baseEnd_7985521 := by
    simpa [prefixWord, tailWord_7985521, baseEnd_7985521] using wordTrace_append hprefix tailTrace_7985521
  have hstable : (prefixWord ++ tailWord_7985521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985521).length < 2 ^ (prefixWord ++ tailWord_7985521).sum := by decide
  have hdescent : baseEnd_7985521 < baseStart_7985521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985545 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_7985545 : Nat := 118140960795 + 7985545 * 2 ^ 59
def prefixEnd_7985545 : Nat := 4983230072969 + 3 ^ 40 * 7985545 * 2
def baseEnd_7985545 : Nat := 4100422873108064252162653

theorem tailTrace_7985545 : CollatzResearch.WordTrace tailWord_7985545 prefixEnd_7985545 4100422873108064252162653 := by
  unfold tailWord_7985545
  simp only [CollatzResearch.WordTrace]
  refine ⟨291256753854741762351654089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194171169236494508234436059 291256753854741762351654089)
  ·
    refine ⟨218442565391056321763740567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291256753854741762351654089 218442565391056321763740567)
    ·
      refine ⟨327663848086584482645610851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218442565391056321763740567 327663848086584482645610851)
      ·
        refine ⟨491495772129876723968416277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327663848086584482645610851 491495772129876723968416277)
        ·
          refine ⟨23038864318587971436019513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 491495772129876723968416277 23038864318587971436019513)
          ·
            refine ⟨17279148238940978577014635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23038864318587971436019513 17279148238940978577014635)
            ·
              refine ⟨25918722358411467865521953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17279148238940978577014635 25918722358411467865521953)
              ·
                refine ⟨19439041768808600899141465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25918722358411467865521953 19439041768808600899141465)
                ·
                  refine ⟨14579281326606450674356099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19439041768808600899141465 14579281326606450674356099)
                  ·
                    refine ⟨21868921989909676011534149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14579281326606450674356099 21868921989909676011534149)
                    ·
                      refine ⟨4100422873108064252162653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21868921989909676011534149 4100422873108064252162653)
                      ·
                        rfl

theorem cell23_7985545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_7985545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985545 prefixEnd_7985545 := by exact prefixLift 7985545
  have htrace : WordTrace (prefixWord ++ tailWord_7985545) baseStart_7985545 baseEnd_7985545 := by
    simpa [prefixWord, tailWord_7985545, baseEnd_7985545] using wordTrace_append hprefix tailTrace_7985545
  have hstable : (prefixWord ++ tailWord_7985545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985545).length < 2 ^ (prefixWord ++ tailWord_7985545).sum := by decide
  have hdescent : baseEnd_7985545 < baseStart_7985545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985646 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_7985646 : Nat := 118140960795 + 7985646 * 2 ^ 59
def prefixEnd_7985646 : Nat := 4983230072969 + 3 ^ 40 * 7985646 * 2
def baseEnd_7985646 : Nat := 4100474734654168356999689

theorem tailTrace_7985646 : CollatzResearch.WordTrace tailWord_7985646 prefixEnd_7985646 4100474734654168356999689 := by
  unfold tailWord_7985646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36407554703421982075135099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194173625084917237734053861 36407554703421982075135099)
  ·
    refine ⟨54611332055132973112702649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36407554703421982075135099 54611332055132973112702649)
    ·
      refine ⟨40958499041349729834526987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54611332055132973112702649 40958499041349729834526987)
      ·
        refine ⟨61437748562024594751790481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40958499041349729834526987 61437748562024594751790481)
        ·
          refine ⟨46078311421518446063842861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61437748562024594751790481 46078311421518446063842861)
          ·
            refine ⟨17279366783069417273941073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46078311421518446063842861 17279366783069417273941073)
            ·
              refine ⟨12959525087302062955455805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17279366783069417273941073 12959525087302062955455805)
              ·
                refine ⟨4859821907738273608295927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12959525087302062955455805 4859821907738273608295927)
                ·
                  refine ⟨7289732861607410412443891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859821907738273608295927 7289732861607410412443891)
                  ·
                    refine ⟨10934599292411115618665837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289732861607410412443891 10934599292411115618665837)
                    ·
                      refine ⟨4100474734654168356999689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934599292411115618665837 4100474734654168356999689)
                      ·
                        rfl

theorem cell23_7985646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_7985646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985646 prefixEnd_7985646 := by exact prefixLift 7985646
  have htrace : WordTrace (prefixWord ++ tailWord_7985646) baseStart_7985646 baseEnd_7985646 := by
    simpa [prefixWord, tailWord_7985646, baseEnd_7985646] using wordTrace_append hprefix tailTrace_7985646
  have hstable : (prefixWord ++ tailWord_7985646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985646).length < 2 ^ (prefixWord ++ tailWord_7985646).sum := by decide
  have hdescent : baseEnd_7985646 < baseStart_7985646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985692 : List Nat := [2, 2, 3, 1, 2, 4, 2, 7]
def baseStart_7985692 : Nat := 118140960795 + 7985692 * 2 ^ 59
def prefixEnd_7985692 : Nat := 4983230072969 + 3 ^ 40 * 7985692 * 2
def baseEnd_7985692 : Nat := 151870309435713895445351

theorem tailTrace_7985692 : CollatzResearch.WordTrace tailWord_7985692 prefixEnd_7985692 151870309435713895445351 := by
  unfold tailWord_7985692
  simp only [CollatzResearch.WordTrace]
  refine ⟨145631057692604603228627665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194174743590139470971503553 145631057692604603228627665)
  ·
    refine ⟨109223293269453452421470749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145631057692604603228627665 109223293269453452421470749)
    ·
      refine ⟨40958734976045044658051531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109223293269453452421470749 40958734976045044658051531)
      ·
        refine ⟨61438102464067566987077297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40958734976045044658051531 61438102464067566987077297)
        ·
          refine ⟨46078576848050675240307973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61438102464067566987077297 46078576848050675240307973)
          ·
            refine ⟨8639733159009501607557745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46078576848050675240307973 8639733159009501607557745)
            ·
              refine ⟨6479799869257126205668309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639733159009501607557745 6479799869257126205668309)
              ·
                refine ⟨151870309435713895445351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6479799869257126205668309 151870309435713895445351)
                ·
                  rfl

theorem cell23_7985692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 7].length) (baseStart_7985692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985692 prefixEnd_7985692 := by exact prefixLift 7985692
  have htrace : WordTrace (prefixWord ++ tailWord_7985692) baseStart_7985692 baseEnd_7985692 := by
    simpa [prefixWord, tailWord_7985692, baseEnd_7985692] using wordTrace_append hprefix tailTrace_7985692
  have hstable : (prefixWord ++ tailWord_7985692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985692).length < 2 ^ (prefixWord ++ tailWord_7985692).sum := by decide
  have hdescent : baseEnd_7985692 < baseStart_7985692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985708 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_7985708 : Nat := 118140960795 + 7985708 * 2 ^ 59
def prefixEnd_7985708 : Nat := 4983230072969 + 3 ^ 40 * 7985708 * 2
def baseEnd_7985708 : Nat := 4100506570454747114424403

theorem tailTrace_7985708 : CollatzResearch.WordTrace tailWord_7985708 prefixEnd_7985708 4100506570454747114424403 := by
  unfold tailWord_7985708
  simp only [CollatzResearch.WordTrace]
  refine ⟨145631349476575620594918889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194175132635434160793225185 145631349476575620594918889)
  ·
    refine ⟨109223512107431715446189167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145631349476575620594918889 109223512107431715446189167)
    ·
      refine ⟨163835268161147573169283751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109223512107431715446189167 163835268161147573169283751)
      ·
        refine ⟨245752902241721359753925627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163835268161147573169283751 245752902241721359753925627)
        ·
          refine ⟨368629353362582039630888441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245752902241721359753925627 368629353362582039630888441)
          ·
            refine ⟨276472015021936529723166331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368629353362582039630888441 276472015021936529723166331)
            ·
              refine ⟨414708022532904794584749497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276472015021936529723166331 414708022532904794584749497)
              ·
                refine ⟨311031016899678595938562123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414708022532904794584749497 311031016899678595938562123)
                ·
                  refine ⟨466546525349517893907843185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311031016899678595938562123 466546525349517893907843185)
                  ·
                    refine ⟨349909894012138420430882389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466546525349517893907843185 349909894012138420430882389)
                    ·
                      refine ⟨4100506570454747114424403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 349909894012138420430882389 4100506570454747114424403)
                      ·
                        rfl

theorem cell23_7985708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_7985708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985708 prefixEnd_7985708 := by exact prefixLift 7985708
  have htrace : WordTrace (prefixWord ++ tailWord_7985708) baseStart_7985708 baseEnd_7985708 := by
    simpa [prefixWord, tailWord_7985708, baseEnd_7985708] using wordTrace_append hprefix tailTrace_7985708
  have hstable : (prefixWord ++ tailWord_7985708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985708).length < 2 ^ (prefixWord ++ tailWord_7985708).sum := by decide
  have hdescent : baseEnd_7985708 < baseStart_7985708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985745 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_7985745 : Nat := 118140960795 + 7985745 * 2 ^ 59
def prefixEnd_7985745 : Nat := 4983230072969 + 3 ^ 40 * 7985745 * 2
def baseEnd_7985745 : Nat := 4100525569238963469661733

theorem tailTrace_7985745 : CollatzResearch.WordTrace tailWord_7985745 prefixEnd_7985745 4100525569238963469661733 := by
  unfold tailWord_7985745
  simp only [CollatzResearch.WordTrace]
  refine ⟨291264048454017196508934689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194176032302678131005956459 291264048454017196508934689)
  ·
    refine ⟨218448036340512897381701017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291264048454017196508934689 218448036340512897381701017)
    ·
      refine ⟨163836027255384673036275763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218448036340512897381701017 163836027255384673036275763)
      ·
        refine ⟨245754040883077009554413645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163836027255384673036275763 245754040883077009554413645)
        ·
          refine ⟨92157765331153878582905117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245754040883077009554413645 92157765331153878582905117)
          ·
            refine ⟨34559161999182704468589419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92157765331153878582905117 34559161999182704468589419)
            ·
              refine ⟨51838742998774056702884129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34559161999182704468589419 51838742998774056702884129)
              ·
                refine ⟨38879057249080542527163097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51838742998774056702884129 38879057249080542527163097)
                ·
                  refine ⟨29159292936810406895372323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38879057249080542527163097 29159292936810406895372323)
                  ·
                    refine ⟨43738939405215610343058485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29159292936810406895372323 43738939405215610343058485)
                    ·
                      refine ⟨4100525569238963469661733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43738939405215610343058485 4100525569238963469661733)
                      ·
                        rfl

theorem cell23_7985745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_7985745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985745 prefixEnd_7985745 := by exact prefixLift 7985745
  have htrace : WordTrace (prefixWord ++ tailWord_7985745) baseStart_7985745 baseEnd_7985745 := by
    simpa [prefixWord, tailWord_7985745, baseEnd_7985745] using wordTrace_append hprefix tailTrace_7985745
  have hstable : (prefixWord ++ tailWord_7985745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985745).length < 2 ^ (prefixWord ++ tailWord_7985745).sum := by decide
  have hdescent : baseEnd_7985745 < baseStart_7985745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985792 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_7985792 : Nat := 118140960795 + 7985792 * 2 ^ 59
def prefixEnd_7985792 : Nat := 4983230072969 + 3 ^ 40 * 7985792 * 2
def baseEnd_7985792 : Nat := 4100549702829724785774017

theorem tailTrace_7985792 : CollatzResearch.WordTrace tailWord_7985792 prefixEnd_7985792 4100549702829724785774017 := by
  unfold tailWord_7985792
  simp only [CollatzResearch.WordTrace]
  refine ⟨145632881342423461767947815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194177175123231282357263753 145632881342423461767947815)
  ·
    refine ⟨218449322013635192651921723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145632881342423461767947815 218449322013635192651921723)
    ·
      refine ⟨327673983020452788977882585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218449322013635192651921723 327673983020452788977882585)
      ·
        refine ⟨245755487265339591733411939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327673983020452788977882585 245755487265339591733411939)
        ·
          refine ⟨368633230898009387600117909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245755487265339591733411939 368633230898009387600117909)
          ·
            refine ⟨17279682698344190043755527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368633230898009387600117909 17279682698344190043755527)
            ·
              refine ⟨25919524047516285065633291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17279682698344190043755527 25919524047516285065633291)
              ·
                refine ⟨38879286071274427598449937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25919524047516285065633291 38879286071274427598449937)
                ·
                  refine ⟨29159464553455820698837453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38879286071274427598449937 29159464553455820698837453)
                  ·
                    refine ⟨10934799207545932762064045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29159464553455820698837453 10934799207545932762064045)
                    ·
                      refine ⟨4100549702829724785774017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934799207545932762064045 4100549702829724785774017)
                      ·
                        rfl

theorem cell23_7985792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_7985792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985792 prefixEnd_7985792 := by exact prefixLift 7985792
  have htrace : WordTrace (prefixWord ++ tailWord_7985792) baseStart_7985792 baseEnd_7985792 := by
    simpa [prefixWord, tailWord_7985792, baseEnd_7985792] using wordTrace_append hprefix tailTrace_7985792
  have hstable : (prefixWord ++ tailWord_7985792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985792).length < 2 ^ (prefixWord ++ tailWord_7985792).sum := by decide
  have hdescent : baseEnd_7985792 < baseStart_7985792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985795 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 4, 5]
def baseStart_7985795 : Nat := 118140960795 + 7985795 * 2 ^ 59
def prefixEnd_7985795 : Nat := 4983230072969 + 3 ^ 40 * 7985795 * 2
def baseEnd_7985795 : Nat := 1366850414423896091345501

theorem tailTrace_7985795 : CollatzResearch.WordTrace tailWord_7985795 prefixEnd_7985795 1366850414423896091345501 := by
  unfold tailWord_7985795
  simp only [CollatzResearch.WordTrace]
  refine ⟨291265872103836055048254839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194177248069224036698836559 291265872103836055048254839)
  ·
    refine ⟨436898808155754082572382259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291265872103836055048254839 436898808155754082572382259)
    ·
      refine ⟨655348212233631123858573389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436898808155754082572382259 655348212233631123858573389)
      ·
        refine ⟨245755579587611671446965021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655348212233631123858573389 245755579587611671446965021)
        ·
          refine ⟨92158342345354376792611883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245755579587611671446965021 92158342345354376792611883)
          ·
            refine ⟨138237513518031565188917825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92158342345354376792611883 138237513518031565188917825)
            ·
              refine ⟨103678135138523673891688369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138237513518031565188917825 103678135138523673891688369)
              ·
                refine ⟨77758601353892755418766277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103678135138523673891688369 77758601353892755418766277)
                ·
                  refine ⟨14579737753854891641018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77758601353892755418766277 14579737753854891641018677)
                  ·
                    refine ⟨1366850414423896091345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14579737753854891641018677 1366850414423896091345501)
                    ·
                      rfl

theorem cell23_7985795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].length) (baseStart_7985795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985795 prefixEnd_7985795 := by exact prefixLift 7985795
  have htrace : WordTrace (prefixWord ++ tailWord_7985795) baseStart_7985795 baseEnd_7985795 := by
    simpa [prefixWord, tailWord_7985795, baseEnd_7985795] using wordTrace_append hprefix tailTrace_7985795
  have hstable : (prefixWord ++ tailWord_7985795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985795).length < 2 ^ (prefixWord ++ tailWord_7985795).sum := by decide
  have hdescent : baseEnd_7985795 < baseStart_7985795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985852 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7985852 : Nat := 118140960795 + 7985852 * 2 ^ 59
def prefixEnd_7985852 : Nat := 4983230072969 + 3 ^ 40 * 7985852 * 2
def baseEnd_7985852 : Nat := 4100580511668994551023741

theorem tailTrace_7985852 : CollatzResearch.WordTrace tailWord_7985852 prefixEnd_7985852 4100580511668994551023741 := by
  unfold tailWord_7985852
  simp only [CollatzResearch.WordTrace]
  refine ⟨145633975532314776891539905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194178634043086369188719873 145633975532314776891539905)
  ·
    refine ⟨109225481649236082668654929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145633975532314776891539905 109225481649236082668654929)
    ·
      refine ⟨81919111236927062001491197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109225481649236082668654929 81919111236927062001491197)
      ·
        refine ⟨30719666713847648250559199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81919111236927062001491197 30719666713847648250559199)
        ·
          refine ⟨46079500070771472375838799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30719666713847648250559199 46079500070771472375838799)
          ·
            refine ⟨69119250106157208563758199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46079500070771472375838799 69119250106157208563758199)
            ·
              refine ⟨103678875159235812845637299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69119250106157208563758199 103678875159235812845637299)
              ·
                refine ⟨155518312738853719268455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103678875159235812845637299 155518312738853719268455949)
                ·
                  refine ⟨58319367277070144725670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155518312738853719268455949 58319367277070144725670981)
                  ·
                    refine ⟨10934881364450652136063309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58319367277070144725670981 10934881364450652136063309)
                    ·
                      refine ⟨4100580511668994551023741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10934881364450652136063309 4100580511668994551023741)
                      ·
                        rfl

theorem cell23_7985852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7985852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985852 prefixEnd_7985852 := by exact prefixLift 7985852
  have htrace : WordTrace (prefixWord ++ tailWord_7985852) baseStart_7985852 baseEnd_7985852 := by
    simpa [prefixWord, tailWord_7985852, baseEnd_7985852] using wordTrace_append hprefix tailTrace_7985852
  have hstable : (prefixWord ++ tailWord_7985852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985852).length < 2 ^ (prefixWord ++ tailWord_7985852).sum := by decide
  have hdescent : baseEnd_7985852 < baseStart_7985852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985893 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_7985893 : Nat := 118140960795 + 7985893 * 2 ^ 59
def prefixEnd_7985893 : Nat := 4983230072969 + 3 ^ 40 * 7985893 * 2
def baseEnd_7985893 : Nat := 1366867188125276296870351

theorem tailTrace_7985893 : CollatzResearch.WordTrace tailWord_7985893 prefixEnd_7985893 1366867188125276296870351 := by
  unfold tailWord_7985893
  simp only [CollatzResearch.WordTrace]
  refine ⟨291269446457481017785322333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194179630971654011856881555 291269446457481017785322333)
  ·
    refine ⟨109226042421555381669495875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291269446457481017785322333 109226042421555381669495875)
    ·
      refine ⟨163839063632333072504243813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109226042421555381669495875 163839063632333072504243813)
      ·
        refine ⟨30719824431062451094545715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163839063632333072504243813 30719824431062451094545715)
        ·
          refine ⟨46079736646593676641818573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30719824431062451094545715 46079736646593676641818573)
          ·
            refine ⟨17279901242472628740681965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46079736646593676641818573 17279901242472628740681965)
            ·
              refine ⟨6479962965927235777755737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17279901242472628740681965 6479962965927235777755737)
              ·
                refine ⟨4859972224445426833316803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479962965927235777755737 4859972224445426833316803)
                ·
                  refine ⟨7289958336668140249975205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859972224445426833316803 7289958336668140249975205)
                  ·
                    refine ⟨1366867188125276296870351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7289958336668140249975205 1366867188125276296870351)
                    ·
                      rfl

theorem cell23_7985893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_7985893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985893 prefixEnd_7985893 := by exact prefixLift 7985893
  have htrace : WordTrace (prefixWord ++ tailWord_7985893) baseStart_7985893 baseEnd_7985893 := by
    simpa [prefixWord, tailWord_7985893, baseEnd_7985893] using wordTrace_append hprefix tailTrace_7985893
  have hstable : (prefixWord ++ tailWord_7985893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985893).length < 2 ^ (prefixWord ++ tailWord_7985893).sum := by decide
  have hdescent : baseEnd_7985893 < baseStart_7985893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985906 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_7985906 : Nat := 118140960795 + 7985906 * 2 ^ 59
def prefixEnd_7985906 : Nat := 4983230072969 + 3 ^ 40 * 7985906 * 2
def baseEnd_7985906 : Nat := 455623137736037482194277

theorem tailTrace_7985906 : CollatzResearch.WordTrace tailWord_7985906 prefixEnd_7985906 455623137736037482194277 := by
  unfold tailWord_7985906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72817480151608480251386393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194179947070955947337030381 72817480151608480251386393)
  ·
    refine ⟨54613110113706360188539795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72817480151608480251386393 54613110113706360188539795)
    ·
      refine ⟨81919665170559540282809693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54613110113706360188539795 81919665170559540282809693)
      ·
        refine ⟨30719874438959827606053635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81919665170559540282809693 30719874438959827606053635)
        ·
          refine ⟨46079811658439741409080453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30719874438959827606053635 46079811658439741409080453)
          ·
            refine ⟨8639964685957451514202585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46079811658439741409080453 8639964685957451514202585)
            ·
              refine ⟨6479973514468088635651939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639964685957451514202585 6479973514468088635651939)
              ·
                refine ⟨9719960271702132953477909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479973514468088635651939 9719960271702132953477909)
                ·
                  refine ⟨455623137736037482194277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9719960271702132953477909 455623137736037482194277)
                  ·
                    rfl

theorem cell23_7985906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_7985906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985906 prefixEnd_7985906 := by exact prefixLift 7985906
  have htrace : WordTrace (prefixWord ++ tailWord_7985906) baseStart_7985906 baseEnd_7985906 := by
    simpa [prefixWord, tailWord_7985906, baseEnd_7985906] using wordTrace_append hprefix tailTrace_7985906
  have hstable : (prefixWord ++ tailWord_7985906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985906).length < 2 ^ (prefixWord ++ tailWord_7985906).sum := by decide
  have hdescent : baseEnd_7985906 < baseStart_7985906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985966 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7985966 : Nat := 118140960795 + 7985966 * 2 ^ 59
def prefixEnd_7985966 : Nat := 4983230072969 + 3 ^ 40 * 7985966 * 2
def baseEnd_7985966 : Nat := 1366879682821202368332739

theorem tailTrace_7985966 : CollatzResearch.WordTrace tailWord_7985966 prefixEnd_7985966 1366879682821202368332739 := by
  unfold tailWord_7985966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36409013623277068906591219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194181405990811034168486501 36409013623277068906591219)
  ·
    refine ⟨54613520434915603359886829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36409013623277068906591219 54613520434915603359886829)
    ·
      refine ⟨20480070163093351259957561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54613520434915603359886829 20480070163093351259957561)
      ·
        refine ⟨15360052622320013444968171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20480070163093351259957561 15360052622320013444968171)
        ·
          refine ⟨23040078933480020167452257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15360052622320013444968171 23040078933480020167452257)
          ·
            refine ⟨17280059200110015125589193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23040078933480020167452257 17280059200110015125589193)
            ·
              refine ⟨12960044400082511344191895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280059200110015125589193 12960044400082511344191895)
              ·
                refine ⟨19440066600123767016287843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960044400082511344191895 19440066600123767016287843)
                ·
                  refine ⟨29160099900185650524431765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19440066600123767016287843 29160099900185650524431765)
                  ·
                    refine ⟨1366879682821202368332739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29160099900185650524431765 1366879682821202368332739)
                    ·
                      rfl

theorem cell23_7985966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7985966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985966 prefixEnd_7985966 := by exact prefixLift 7985966
  have htrace : WordTrace (prefixWord ++ tailWord_7985966) baseStart_7985966 baseEnd_7985966 := by
    simpa [prefixWord, tailWord_7985966, baseEnd_7985966] using wordTrace_append hprefix tailTrace_7985966
  have hstable : (prefixWord ++ tailWord_7985966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985966).length < 2 ^ (prefixWord ++ tailWord_7985966).sum := by decide
  have hdescent : baseEnd_7985966 < baseStart_7985966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985969 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_7985969 : Nat := 118140960795 + 7985969 * 2 ^ 59
def prefixEnd_7985969 : Nat := 4983230072969 + 3 ^ 40 * 7985969 * 2
def baseEnd_7985969 : Nat := 4100640588905570593260703

theorem tailTrace_7985969 : CollatzResearch.WordTrace tailWord_7985969 prefixEnd_7985969 4100640588905570593260703 := by
  unfold tailWord_7985969
  simp only [CollatzResearch.WordTrace]
  refine ⟨291272218405205682765088961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194181478936803788510059307 291272218405205682765088961)
  ·
    refine ⟨218454163803904262073816721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291272218405205682765088961 218454163803904262073816721)
    ·
      refine ⟨163840622852928196555362541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218454163803904262073816721 163840622852928196555362541)
      ·
        refine ⟨61440233569848073708260953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163840622852928196555362541 61440233569848073708260953)
        ·
          refine ⟨46080175177386055281195715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61440233569848073708260953 46080175177386055281195715)
          ·
            refine ⟨69120262766079082921793573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46080175177386055281195715 69120262766079082921793573)
            ·
              refine ⟨12960049268639828047836295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69120262766079082921793573 12960049268639828047836295)
              ·
                refine ⟨19440073902959742071754443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960049268639828047836295 19440073902959742071754443)
                ·
                  refine ⟨29160110854439613107631665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19440073902959742071754443 29160110854439613107631665)
                  ·
                    refine ⟨21870083140829709830723749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29160110854439613107631665 21870083140829709830723749)
                    ·
                      refine ⟨4100640588905570593260703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21870083140829709830723749 4100640588905570593260703)
                      ·
                        rfl

theorem cell23_7985969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_7985969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985969 prefixEnd_7985969 := by exact prefixLift 7985969
  have htrace : WordTrace (prefixWord ++ tailWord_7985969) baseStart_7985969 baseEnd_7985969 := by
    simpa [prefixWord, tailWord_7985969, baseEnd_7985969] using wordTrace_append hprefix tailTrace_7985969
  have hstable : (prefixWord ++ tailWord_7985969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985969).length < 2 ^ (prefixWord ++ tailWord_7985969).sum := by decide
  have hdescent : baseEnd_7985969 < baseStart_7985969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985973 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_7985973 : Nat := 118140960795 + 7985973 * 2 ^ 59
def prefixEnd_7985973 : Nat := 4983230072969 + 3 ^ 40 * 7985973 * 2
def baseEnd_7985973 : Nat := 4100642642828188577610685

theorem tailTrace_7985973 : CollatzResearch.WordTrace tailWord_7985973 prefixEnd_7985973 4100642642828188577610685 := by
  unfold tailWord_7985973
  simp only [CollatzResearch.WordTrace]
  refine ⟨291272364297191191448234573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194181576198127460965489715 291272364297191191448234573)
  ·
    refine ⟨109227136611446696793087965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291272364297191191448234573 109227136611446696793087965)
    ·
      refine ⟨40960176229292511297407987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109227136611446696793087965 40960176229292511297407987)
      ·
        refine ⟨61440264343938766946111981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40960176229292511297407987 61440264343938766946111981)
        ·
          refine ⟨23040099128977037604791993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61440264343938766946111981 23040099128977037604791993)
          ·
            refine ⟨17280074346732778203593995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23040099128977037604791993 17280074346732778203593995)
            ·
              refine ⟨25920111520099167305390993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280074346732778203593995 25920111520099167305390993)
              ·
                refine ⟨19440083640074375479043245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25920111520099167305390993 19440083640074375479043245)
                ·
                  refine ⟨7290031365027890804641217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19440083640074375479043245 7290031365027890804641217)
                  ·
                    refine ⟨5467523523770918103480913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290031365027890804641217 5467523523770918103480913)
                    ·
                      refine ⟨4100642642828188577610685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467523523770918103480913 4100642642828188577610685)
                      ·
                        rfl

theorem cell23_7985973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_7985973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985973 prefixEnd_7985973 := by exact prefixLift 7985973
  have htrace : WordTrace (prefixWord ++ tailWord_7985973) baseStart_7985973 baseEnd_7985973 := by
    simpa [prefixWord, tailWord_7985973, baseEnd_7985973] using wordTrace_append hprefix tailTrace_7985973
  have hstable : (prefixWord ++ tailWord_7985973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985973).length < 2 ^ (prefixWord ++ tailWord_7985973).sum := by decide
  have hdescent : baseEnd_7985973 < baseStart_7985973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985990 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7985990 : Nat := 118140960795 + 7985990 * 2 ^ 59
def prefixEnd_7985990 : Nat := 4983230072969 + 3 ^ 40 * 7985990 * 2
def baseEnd_7985990 : Nat := 4100651371999315011098107

theorem tailTrace_7985990 : CollatzResearch.WordTrace tailWord_7985990 prefixEnd_7985990 4100651371999315011098107 := by
  unfold tailWord_7985990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102280760566550104737607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194181989558753068901068949 9102280760566550104737607)
  ·
    refine ⟨13653421140849825157106411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9102280760566550104737607 13653421140849825157106411)
    ·
      refine ⟨20480131711274737735659617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13653421140849825157106411 20480131711274737735659617)
      ·
        refine ⟨15360098783456053301744713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20480131711274737735659617 15360098783456053301744713)
        ·
          refine ⟨11520074087592039976308535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15360098783456053301744713 11520074087592039976308535)
          ·
            refine ⟨17280111131388059964462803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520074087592039976308535 17280111131388059964462803)
            ·
              refine ⟨25920166697082089946694205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280111131388059964462803 25920166697082089946694205)
              ·
                refine ⟨9720062511405783730010327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25920166697082089946694205 9720062511405783730010327)
                ·
                  refine ⟨14580093767108675595015491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720062511405783730010327 14580093767108675595015491)
                  ·
                    refine ⟨21870140650663013392523237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14580093767108675595015491 21870140650663013392523237)
                    ·
                      refine ⟨4100651371999315011098107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21870140650663013392523237 4100651371999315011098107)
                      ·
                        rfl

theorem cell23_7985990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7985990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985990 prefixEnd_7985990 := by exact prefixLift 7985990
  have htrace : WordTrace (prefixWord ++ tailWord_7985990) baseStart_7985990 baseEnd_7985990 := by
    simpa [prefixWord, tailWord_7985990, baseEnd_7985990] using wordTrace_append hprefix tailTrace_7985990
  have hstable : (prefixWord ++ tailWord_7985990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985990).length < 2 ^ (prefixWord ++ tailWord_7985990).sum := by decide
  have hdescent : baseEnd_7985990 < baseStart_7985990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985993 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 1, 2, 3]
def baseStart_7985993 : Nat := 118140960795 + 7985993 * 2 ^ 59
def prefixEnd_7985993 : Nat := 4983230072969 + 3 ^ 40 * 7985993 * 2
def baseEnd_7985993 : Nat := 4100652912441278499360593

theorem tailTrace_7985993 : CollatzResearch.WordTrace tailWord_7985993 prefixEnd_7985993 4100652912441278499360593 := by
  unfold tailWord_7985993
  simp only [CollatzResearch.WordTrace]
  refine ⟨291273093757118734863962633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194182062504745823242641755 291273093757118734863962633)
  ·
    refine ⟨218454820317839051147971975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291273093757118734863962633 218454820317839051147971975)
    ·
      refine ⟨327682230476758576721957963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218454820317839051147971975 327682230476758576721957963)
      ·
        refine ⟨491523345715137865082936945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327682230476758576721957963 491523345715137865082936945)
        ·
          refine ⟨368642509286353398812202709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491523345715137865082936945 368642509286353398812202709)
          ·
            refine ⟨8640058811398907784661001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368642509286353398812202709 8640058811398907784661001)
            ·
              refine ⟨6480044108549180838495751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640058811398907784661001 6480044108549180838495751)
              ·
                refine ⟨9720066162823771257743627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480044108549180838495751 9720066162823771257743627)
                ·
                  refine ⟨14580099244235656886615441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720066162823771257743627 14580099244235656886615441)
                  ·
                    refine ⟨10935074433176742664961581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14580099244235656886615441 10935074433176742664961581)
                    ·
                      refine ⟨4100652912441278499360593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10935074433176742664961581 4100652912441278499360593)
                      ·
                        rfl

theorem cell23_7985993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 2, 3].length) (baseStart_7985993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7985993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7985993 prefixEnd_7985993 := by exact prefixLift 7985993
  have htrace : WordTrace (prefixWord ++ tailWord_7985993) baseStart_7985993 baseEnd_7985993 := by
    simpa [prefixWord, tailWord_7985993, baseEnd_7985993] using wordTrace_append hprefix tailTrace_7985993
  have hstable : (prefixWord ++ tailWord_7985993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985993).length < 2 ^ (prefixWord ++ tailWord_7985993).sum := by decide
  have hdescent : baseEnd_7985993 < baseStart_7985993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986033 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_7986033 : Nat := 118140960795 + 7986033 * 2 ^ 59
def prefixEnd_7986033 : Nat := 4983230072969 + 3 ^ 40 * 7986033 * 2
def baseEnd_7986033 : Nat := 4100673451667458342860409

theorem tailTrace_7986033 : CollatzResearch.WordTrace tailWord_7986033 prefixEnd_7986033 4100673451667458342860409 := by
  unfold tailWord_7986033
  simp only [CollatzResearch.WordTrace]
  refine ⟨291274552676973821695418753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194183035117982547796945835 291274552676973821695418753)
  ·
    refine ⟨218455914507730366271564065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291274552676973821695418753 218455914507730366271564065)
    ·
      refine ⟨163841935880797774703673049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218455914507730366271564065 163841935880797774703673049)
      ·
        refine ⟨122881451910598331027754787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163841935880797774703673049 122881451910598331027754787)
        ·
          refine ⟨184322177865897496541632181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122881451910598331027754787 184322177865897496541632181)
          ·
            refine ⟨17280204174927890300778017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184322177865897496541632181 17280204174927890300778017)
            ·
              refine ⟨12960153131195917725583513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280204174927890300778017 12960153131195917725583513)
              ·
                refine ⟨9720114848396938294187635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12960153131195917725583513 9720114848396938294187635)
                ·
                  refine ⟨14580172272595407441281453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720114848396938294187635 14580172272595407441281453)
                  ·
                    refine ⟨5467564602223277790480545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14580172272595407441281453 5467564602223277790480545)
                    ·
                      refine ⟨4100673451667458342860409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467564602223277790480545 4100673451667458342860409)
                      ·
                        rfl

theorem cell23_7986033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_7986033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986033 prefixEnd_7986033 := by exact prefixLift 7986033
  have htrace : WordTrace (prefixWord ++ tailWord_7986033) baseStart_7986033 baseEnd_7986033 := by
    simpa [prefixWord, tailWord_7986033, baseEnd_7986033] using wordTrace_append hprefix tailTrace_7986033
  have hstable : (prefixWord ++ tailWord_7986033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986033).length < 2 ^ (prefixWord ++ tailWord_7986033).sum := by decide
  have hdescent : baseEnd_7986033 < baseStart_7986033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986069 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 7]
def baseStart_7986069 : Nat := 118140960795 + 7986069 * 2 ^ 59
def prefixEnd_7986069 : Nat := 4983230072969 + 3 ^ 40 * 7986069 * 2
def baseEnd_7986069 : Nat := 455632437441224466890027

theorem tailTrace_7986069 : CollatzResearch.WordTrace tailWord_7986069 prefixEnd_7986069 455632437441224466890027 := by
  unfold tailWord_7986069
  simp only [CollatzResearch.WordTrace]
  refine ⟨291275865704843399843729261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194183910469895599895819507 291275865704843399843729261)
  ·
    refine ⟨109228449639316274941398473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291275865704843399843729261 109228449639316274941398473)
    ·
      refine ⟨81921337229487206206048855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109228449639316274941398473 81921337229487206206048855)
      ·
        refine ⟨122882005844230809309073283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81921337229487206206048855 122882005844230809309073283)
        ·
          refine ⟨184323008766346213963609925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122882005844230809309073283 184323008766346213963609925)
          ·
            refine ⟨34560564143689915118176861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184323008766346213963609925 34560564143689915118176861)
            ·
              refine ⟨12960211553883718169316323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34560564143689915118176861 12960211553883718169316323)
              ·
                refine ⟨19440317330825577253974485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960211553883718169316323 19440317330825577253974485)
                ·
                  refine ⟨455632437441224466890027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19440317330825577253974485 455632437441224466890027)
                  ·
                    rfl

theorem cell23_7986069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_7986069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986069 prefixEnd_7986069 := by exact prefixLift 7986069
  have htrace : WordTrace (prefixWord ++ tailWord_7986069) baseStart_7986069 baseEnd_7986069 := by
    simpa [prefixWord, tailWord_7986069, baseEnd_7986069] using wordTrace_append hprefix tailTrace_7986069
  have hstable : (prefixWord ++ tailWord_7986069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986069).length < 2 ^ (prefixWord ++ tailWord_7986069).sum := by decide
  have hdescent : baseEnd_7986069 < baseStart_7986069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986080 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2]
def baseStart_7986080 : Nat := 118140960795 + 7986080 * 2 ^ 59
def prefixEnd_7986080 : Nat := 4983230072969 + 3 ^ 40 * 7986080 * 2
def baseEnd_7986080 : Nat := 4100697585258219658972693

theorem tailTrace_7986080 : CollatzResearch.WordTrace tailWord_7986080 prefixEnd_7986080 4100697585258219658972693 := by
  unfold tailWord_7986080
  simp only [CollatzResearch.WordTrace]
  refine ⟨145638133453901774361189847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194184177938535699148253129 145638133453901774361189847)
  ·
    refine ⟨218457200180852661541784771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145638133453901774361189847 218457200180852661541784771)
    ·
      refine ⟨327685800271278992312677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218457200180852661541784771 327685800271278992312677157)
      ·
        refine ⟨61441087550864811058626967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327685800271278992312677157 61441087550864811058626967)
        ·
          refine ⟨92161631326297216587940451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61441087550864811058626967 92161631326297216587940451)
          ·
            refine ⟨138242446989445824881910677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92161631326297216587940451 138242446989445824881910677)
            ·
              refine ⟨6480114702630273041339563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138242446989445824881910677 6480114702630273041339563)
              ·
                refine ⟨9720172053945409562009345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480114702630273041339563 9720172053945409562009345)
                ·
                  refine ⟨7290129040459057171507009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9720172053945409562009345 7290129040459057171507009)
                  ·
                    refine ⟨5467596780344292878630257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290129040459057171507009 5467596780344292878630257)
                    ·
                      refine ⟨4100697585258219658972693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467596780344292878630257 4100697585258219658972693)
                      ·
                        rfl

theorem cell23_7986080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_7986080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986080 prefixEnd_7986080 := by exact prefixLift 7986080
  have htrace : WordTrace (prefixWord ++ tailWord_7986080) baseStart_7986080 baseEnd_7986080 := by
    simpa [prefixWord, tailWord_7986080, baseEnd_7986080] using wordTrace_append hprefix tailTrace_7986080
  have hstable : (prefixWord ++ tailWord_7986080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986080).length < 2 ^ (prefixWord ++ tailWord_7986080).sum := by decide
  have hdescent : baseEnd_7986080 < baseStart_7986080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986120 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 5]
def baseStart_7986120 : Nat := 118140960795 + 7986120 * 2 ^ 59
def prefixEnd_7986120 : Nat := 4983230072969 + 3 ^ 40 * 7986120 * 2
def baseEnd_7986120 : Nat := 455635347164933278052501

theorem tailTrace_7986120 : CollatzResearch.WordTrace tailWord_7986120 prefixEnd_7986120 455635347164933278052501 := by
  unfold tailWord_7986120
  simp only [CollatzResearch.WordTrace]
  refine ⟨145638862913829317776917907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194185150551772423702557209 145638862913829317776917907)
  ·
    refine ⟨218458294370743976665376861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145638862913829317776917907 218458294370743976665376861)
    ·
      refine ⟨81921860389028991249516323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218458294370743976665376861 81921860389028991249516323)
      ·
        refine ⟨122882790583543486874274485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81921860389028991249516323 122882790583543486874274485)
        ·
          refine ⟨11520261617207201894463233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122882790583543486874274485 11520261617207201894463233)
          ·
            refine ⟨8640196212905401420847425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520261617207201894463233 8640196212905401420847425)
            ·
              refine ⟨6480147159679051065635569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640196212905401420847425 6480147159679051065635569)
              ·
                refine ⟨4860110369759288299226677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480147159679051065635569 4860110369759288299226677)
                ·
                  refine ⟨455635347164933278052501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860110369759288299226677 455635347164933278052501)
                  ·
                    rfl

theorem cell23_7986120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 5].length) (baseStart_7986120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986120 prefixEnd_7986120 := by exact prefixLift 7986120
  have htrace : WordTrace (prefixWord ++ tailWord_7986120) baseStart_7986120 baseEnd_7986120 := by
    simpa [prefixWord, tailWord_7986120, baseEnd_7986120] using wordTrace_append hprefix tailTrace_7986120
  have hstable : (prefixWord ++ tailWord_7986120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986120).length < 2 ^ (prefixWord ++ tailWord_7986120).sum := by decide
  have hdescent : baseEnd_7986120 < baseStart_7986120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986136 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2]
def baseStart_7986136 : Nat := 118140960795 + 7986136 * 2 ^ 59
def prefixEnd_7986136 : Nat := 4983230072969 + 3 ^ 40 * 7986136 * 2
def baseEnd_7986136 : Nat := 4100726340174871439872435

theorem tailTrace_7986136 : CollatzResearch.WordTrace tailWord_7986136 prefixEnd_7986136 4100726340174871439872435 := by
  unfold tailWord_7986136
  simp only [CollatzResearch.WordTrace]
  refine ⟨145639154697800335143209131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194185539597067113524278841 145639154697800335143209131)
  ·
    refine ⟨218458732046700502714813697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145639154697800335143209131 218458732046700502714813697)
    ·
      refine ⟨163844049035025377036110273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218458732046700502714813697 163844049035025377036110273)
      ·
        refine ⟨122883036776269032777082705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163844049035025377036110273 122883036776269032777082705)
        ·
          refine ⟨92162277582201774582812029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122883036776269032777082705 92162277582201774582812029)
          ·
            refine ⟨34560854093325665468554511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92162277582201774582812029 34560854093325665468554511)
            ·
              refine ⟨51841281139988498202831767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34560854093325665468554511 51841281139988498202831767)
              ·
                refine ⟨77761921709982747304247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51841281139988498202831767 77761921709982747304247651)
                ·
                  refine ⟨116642882564974120956371477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77761921709982747304247651 116642882564974120956371477)
                  ·
                    refine ⟨5467635120233161919829913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116642882564974120956371477 5467635120233161919829913)
                    ·
                      refine ⟨4100726340174871439872435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467635120233161919829913 4100726340174871439872435)
                      ·
                        rfl

theorem cell23_7986136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_7986136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986136 prefixEnd_7986136 := by exact prefixLift 7986136
  have htrace : WordTrace (prefixWord ++ tailWord_7986136) baseStart_7986136 baseEnd_7986136 := by
    simpa [prefixWord, tailWord_7986136, baseEnd_7986136] using wordTrace_append hprefix tailTrace_7986136
  have hstable : (prefixWord ++ tailWord_7986136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986136).length < 2 ^ (prefixWord ++ tailWord_7986136).sum := by decide
  have hdescent : baseEnd_7986136 < baseStart_7986136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986166 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7986166 : Nat := 118140960795 + 7986166 * 2 ^ 59
def prefixEnd_7986166 : Nat := 4983230072969 + 3 ^ 40 * 7986166 * 2
def baseEnd_7986166 : Nat := 4100741744594506322497297

theorem tailTrace_7986166 : CollatzResearch.WordTrace tailWord_7986166 prefixEnd_7986166 4100741744594506322497297 := by
  unfold tailWord_7986166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204962724093249088125647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194186269056994656940006901 18204962724093249088125647)
  ·
    refine ⟨27307444086139873632188471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18204962724093249088125647 27307444086139873632188471)
    ·
      refine ⟨40961166129209810448282707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307444086139873632188471 40961166129209810448282707)
      ·
        refine ⟨61441749193814715672424061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40961166129209810448282707 61441749193814715672424061)
        ·
          refine ⟨23040655947680518377159023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61441749193814715672424061 23040655947680518377159023)
          ·
            refine ⟨34560983921520777565738535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23040655947680518377159023 34560983921520777565738535)
            ·
              refine ⟨51841475882281166348607803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34560983921520777565738535 51841475882281166348607803)
              ·
                refine ⟨77762213823421749522911705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51841475882281166348607803 77762213823421749522911705)
                ·
                  refine ⟨58321660367566312142183779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77762213823421749522911705 58321660367566312142183779)
                  ·
                    refine ⟨87482490551349468213275669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58321660367566312142183779 87482490551349468213275669)
                    ·
                      refine ⟨4100741744594506322497297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87482490551349468213275669 4100741744594506322497297)
                      ·
                        rfl

theorem cell23_7986166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7986166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986166 prefixEnd_7986166 := by exact prefixLift 7986166
  have htrace : WordTrace (prefixWord ++ tailWord_7986166) baseStart_7986166 baseEnd_7986166 := by
    simpa [prefixWord, tailWord_7986166, baseEnd_7986166] using wordTrace_append hprefix tailTrace_7986166
  have hstable : (prefixWord ++ tailWord_7986166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986166).length < 2 ^ (prefixWord ++ tailWord_7986166).sum := by decide
  have hdescent : baseEnd_7986166 < baseStart_7986166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986213 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_7986213 : Nat := 118140960795 + 7986213 * 2 ^ 59
def prefixEnd_7986213 : Nat := 4983230072969 + 3 ^ 40 * 7986213 * 2
def baseEnd_7986213 : Nat := 4100765878185267638609581

theorem tailTrace_7986213 : CollatzResearch.WordTrace tailWord_7986213 prefixEnd_7986213 4100765878185267638609581 := by
  unfold tailWord_7986213
  simp only [CollatzResearch.WordTrace]
  refine ⟨291281117816321712436971293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194187411877547808291314195 291281117816321712436971293)
  ·
    refine ⟨109230419181120642163864235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291281117816321712436971293 109230419181120642163864235)
    ·
      refine ⟨163845628771680963245796353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109230419181120642163864235 163845628771680963245796353)
      ·
        refine ⟨122884221578760722434347265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163845628771680963245796353 122884221578760722434347265)
        ·
          refine ⟨92163166184070541825760449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122884221578760722434347265 92163166184070541825760449)
          ·
            refine ⟨69122374638052906369320337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92163166184070541825760449 69122374638052906369320337)
            ·
              refine ⟨51841780978539679776990253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69122374638052906369320337 51841780978539679776990253)
              ·
                refine ⟨19440667866952379916371345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51841780978539679776990253 19440667866952379916371345)
                ·
                  refine ⟨14580500900214284937278509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19440667866952379916371345 14580500900214284937278509)
                  ·
                    refine ⟨5467687837580356851479441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14580500900214284937278509 5467687837580356851479441)
                    ·
                      refine ⟨4100765878185267638609581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467687837580356851479441 4100765878185267638609581)
                      ·
                        rfl

theorem cell23_7986213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_7986213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986213 prefixEnd_7986213 := by exact prefixLift 7986213
  have htrace : WordTrace (prefixWord ++ tailWord_7986213) baseStart_7986213 baseEnd_7986213 := by
    simpa [prefixWord, tailWord_7986213, baseEnd_7986213] using wordTrace_append hprefix tailTrace_7986213
  have hstable : (prefixWord ++ tailWord_7986213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986213).length < 2 ^ (prefixWord ++ tailWord_7986213).sum := by decide
  have hdescent : baseEnd_7986213 < baseStart_7986213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986219 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 6]
def baseStart_7986219 : Nat := 118140960795 + 7986219 * 2 ^ 59
def prefixEnd_7986219 : Nat := 4983230072969 + 3 ^ 40 * 7986219 * 2
def baseEnd_7986219 : Nat := 1366922986356398205044851

theorem tailTrace_7986219 : CollatzResearch.WordTrace tailWord_7986219 prefixEnd_7986219 1366922986356398205044851 := by
  unfold tailWord_7986219
  simp only [CollatzResearch.WordTrace]
  refine ⟨291281336654299975461689711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194187557769533316974459807 291281336654299975461689711)
  ·
    refine ⟨436922004981449963192534567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291281336654299975461689711 436922004981449963192534567)
    ·
      refine ⟨655383007472174944788801851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436922004981449963192534567 655383007472174944788801851)
      ·
        refine ⟨983074511208262417183202777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655383007472174944788801851 983074511208262417183202777)
        ·
          refine ⟨737305883406196812887402083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983074511208262417183202777 737305883406196812887402083)
          ·
            refine ⟨1105958825109295219331103125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737305883406196812887402083 1105958825109295219331103125)
            ·
              refine ⟨51841819926998213406145459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1105958825109295219331103125 51841819926998213406145459)
              ·
                refine ⟨77762729890497320109218189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51841819926998213406145459 77762729890497320109218189)
                ·
                  refine ⟨29161023708936495040956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77762729890497320109218189 29161023708936495040956821)
                  ·
                    refine ⟨1366922986356398205044851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29161023708936495040956821 1366922986356398205044851)
                    ·
                      rfl

theorem cell23_7986219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_7986219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986219 prefixEnd_7986219 := by exact prefixLift 7986219
  have htrace : WordTrace (prefixWord ++ tailWord_7986219) baseStart_7986219 baseEnd_7986219 := by
    simpa [prefixWord, tailWord_7986219, baseEnd_7986219] using wordTrace_append hprefix tailTrace_7986219
  have hstable : (prefixWord ++ tailWord_7986219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986219).length < 2 ^ (prefixWord ++ tailWord_7986219).sum := by decide
  have hdescent : baseEnd_7986219 < baseStart_7986219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986230 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_7986230 : Nat := 118140960795 + 7986230 * 2 ^ 59
def prefixEnd_7986230 : Nat := 4983230072969 + 3 ^ 40 * 7986230 * 2
def baseEnd_7986230 : Nat := 4100774607356394072097003

theorem tailTrace_7986230 : CollatzResearch.WordTrace tailWord_7986230 prefixEnd_7986230 4100774607356394072097003 := by
  unfold tailWord_7986230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18205108616078757771271259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194187825238173416226893429 18205108616078757771271259)
  ·
    refine ⟨27307662924118136656906889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18205108616078757771271259 27307662924118136656906889)
    ·
      refine ⟨20480747193088602492680167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27307662924118136656906889 20480747193088602492680167)
      ·
        refine ⟨30721120789632903739020251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20480747193088602492680167 30721120789632903739020251)
        ·
          refine ⟨46081681184449355608530377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30721120789632903739020251 46081681184449355608530377)
          ·
            refine ⟨34561260888337016706397783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46081681184449355608530377 34561260888337016706397783)
            ·
              refine ⟨51841891332505525059596675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34561260888337016706397783 51841891332505525059596675)
              ·
                refine ⟨77762836998758287589395013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51841891332505525059596675 77762836998758287589395013)
                ·
                  refine ⟨14580531937267178923011565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77762836998758287589395013 14580531937267178923011565)
                  ·
                    refine ⟨5467699476475192096129337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14580531937267178923011565 5467699476475192096129337)
                    ·
                      refine ⟨4100774607356394072097003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467699476475192096129337 4100774607356394072097003)
                      ·
                        rfl

theorem cell23_7986230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_7986230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986230 prefixEnd_7986230 := by exact prefixLift 7986230
  have htrace : WordTrace (prefixWord ++ tailWord_7986230) baseStart_7986230 baseEnd_7986230 := by
    simpa [prefixWord, tailWord_7986230, baseEnd_7986230] using wordTrace_append hprefix tailTrace_7986230
  have hstable : (prefixWord ++ tailWord_7986230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986230).length < 2 ^ (prefixWord ++ tailWord_7986230).sum := by decide
  have hdescent : baseEnd_7986230 < baseStart_7986230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986260 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_7986260 : Nat := 118140960795 + 7986260 * 2 ^ 59
def prefixEnd_7986260 : Nat := 4983230072969 + 3 ^ 40 * 7986260 * 2
def baseEnd_7986260 : Nat := 4100790011776028954721865

theorem tailTrace_7986260 : CollatzResearch.WordTrace tailWord_7986260 prefixEnd_7986260 4100790011776028954721865 := by
  unfold tailWord_7986260
  simp only [CollatzResearch.WordTrace]
  refine ⟨145641416023575719731966117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194188554698100959642621489 145641416023575719731966117)
  ·
    refine ⟨27307765504420447449743647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145641416023575719731966117 27307765504420447449743647)
    ·
      refine ⟨40961648256630671174615471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307765504420447449743647 40961648256630671174615471)
      ·
        refine ⟨61442472384946006761923207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40961648256630671174615471 61442472384946006761923207)
        ·
          refine ⟨92163708577419010142884811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61442472384946006761923207 92163708577419010142884811)
          ·
            refine ⟨138245562866128515214327217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92163708577419010142884811 138245562866128515214327217)
            ·
              refine ⟨103684172149596386410745413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138245562866128515214327217 103684172149596386410745413)
              ·
                refine ⟨19440782278049322452014765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103684172149596386410745413 19440782278049322452014765)
                ·
                  refine ⟨7290293354268495919505537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19440782278049322452014765 7290293354268495919505537)
                  ·
                    refine ⟨5467720015701371939629153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290293354268495919505537 5467720015701371939629153)
                    ·
                      refine ⟨4100790011776028954721865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467720015701371939629153 4100790011776028954721865)
                      ·
                        rfl

theorem cell23_7986260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_7986260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986260 prefixEnd_7986260 := by exact prefixLift 7986260
  have htrace : WordTrace (prefixWord ++ tailWord_7986260) baseStart_7986260 baseEnd_7986260 := by
    simpa [prefixWord, tailWord_7986260, baseEnd_7986260] using wordTrace_append hprefix tailTrace_7986260
  have hstable : (prefixWord ++ tailWord_7986260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986260).length < 2 ^ (prefixWord ++ tailWord_7986260).sum := by decide
  have hdescent : baseEnd_7986260 < baseStart_7986260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986270 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7986270 : Nat := 118140960795 + 7986270 * 2 ^ 59
def prefixEnd_7986270 : Nat := 4983230072969 + 3 ^ 40 * 7986270 * 2
def baseEnd_7986270 : Nat := 1366931715527524638532273

theorem tailTrace_7986270 : CollatzResearch.WordTrace tailWord_7986270 prefixEnd_7986270 1366931715527524638532273 := by
  unfold tailWord_7986270
  simp only [CollatzResearch.WordTrace]
  refine ⟨36410399597139401396474533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194188797851410140781197509 36410399597139401396474533)
  ·
    refine ⟨6826949924463637761838975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36410399597139401396474533 6826949924463637761838975)
    ·
      refine ⟨10240424886695456642758463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826949924463637761838975 10240424886695456642758463)
      ·
        refine ⟨15360637330043184964137695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240424886695456642758463 15360637330043184964137695)
        ·
          refine ⟨23040955995064777446206543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15360637330043184964137695 23040955995064777446206543)
          ·
            refine ⟨34561433992597166169309815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23040955995064777446206543 34561433992597166169309815)
            ·
              refine ⟨51842150988895749253964723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34561433992597166169309815 51842150988895749253964723)
              ·
                refine ⟨77763226483343623880947085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51842150988895749253964723 77763226483343623880947085)
                ·
                  refine ⟨29161209931253858955355157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77763226483343623880947085 29161209931253858955355157)
                  ·
                    refine ⟨1366931715527524638532273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29161209931253858955355157 1366931715527524638532273)
                    ·
                      rfl

theorem cell23_7986270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7986270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986270 prefixEnd_7986270 := by exact prefixLift 7986270
  have htrace : WordTrace (prefixWord ++ tailWord_7986270) baseStart_7986270 baseEnd_7986270 := by
    simpa [prefixWord, tailWord_7986270, baseEnd_7986270] using wordTrace_append hprefix tailTrace_7986270
  have hstable : (prefixWord ++ tailWord_7986270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986270).length < 2 ^ (prefixWord ++ tailWord_7986270).sum := by decide
  have hdescent : baseEnd_7986270 < baseStart_7986270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986277 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_7986277 : Nat := 118140960795 + 7986277 * 2 ^ 59
def prefixEnd_7986277 : Nat := 4983230072969 + 3 ^ 40 * 7986277 * 2
def baseEnd_7986277 : Nat := 4100798740947155388209287

theorem tailTrace_7986277 : CollatzResearch.WordTrace tailWord_7986277 prefixEnd_7986277 4100798740947155388209287 := by
  unfold tailWord_7986277
  simp only [CollatzResearch.WordTrace]
  refine ⟨291283452088089851367301085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194188968058726567578200723 291283452088089851367301085)
  ·
    refine ⟨109231294533033694262737907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291283452088089851367301085 109231294533033694262737907)
    ·
      refine ⟨163846941799550541394106861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109231294533033694262737907 163846941799550541394106861)
      ·
        refine ⟨61442603174831453022790073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163846941799550541394106861 61442603174831453022790073)
        ·
          refine ⟨46081952381123589767092555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61442603174831453022790073 46081952381123589767092555)
          ·
            refine ⟨69122928571685384650638833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46081952381123589767092555 69122928571685384650638833)
            ·
              refine ⟨51842196428764038487979125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69122928571685384650638833 51842196428764038487979125)
              ·
                refine ⟨4860205915196628608248043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51842196428764038487979125 4860205915196628608248043)
                ·
                  refine ⟨7290308872794942912372065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860205915196628608248043 7290308872794942912372065)
                  ·
                    refine ⟨5467731654596207184279049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290308872794942912372065 5467731654596207184279049)
                    ·
                      refine ⟨4100798740947155388209287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467731654596207184279049 4100798740947155388209287)
                      ·
                        rfl

theorem cell23_7986277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_7986277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986277 prefixEnd_7986277 := by exact prefixLift 7986277
  have htrace : WordTrace (prefixWord ++ tailWord_7986277) baseStart_7986277 baseEnd_7986277 := by
    simpa [prefixWord, tailWord_7986277, baseEnd_7986277] using wordTrace_append hprefix tailTrace_7986277
  have hstable : (prefixWord ++ tailWord_7986277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986277).length < 2 ^ (prefixWord ++ tailWord_7986277).sum := by decide
  have hdescent : baseEnd_7986277 < baseStart_7986277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986294 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7986294 : Nat := 118140960795 + 7986294 * 2 ^ 59
def prefixEnd_7986294 : Nat := 4983230072969 + 3 ^ 40 * 7986294 * 2
def baseEnd_7986294 : Nat := 4100807470118281821696709

theorem tailTrace_7986294 : CollatzResearch.WordTrace tailWord_7986294 prefixEnd_7986294 4100807470118281821696709 := by
  unfold tailWord_7986294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18205254508064266454416871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194189381419352175513779957 18205254508064266454416871)
  ·
    refine ⟨27307881762096399681625307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18205254508064266454416871 27307881762096399681625307)
    ·
      refine ⟨40961822643144599522437961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307881762096399681625307 40961822643144599522437961)
      ·
        refine ⟨30721366982358449641828471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40961822643144599522437961 30721366982358449641828471)
        ·
          refine ⟨46082050473537674462742707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30721366982358449641828471 46082050473537674462742707)
          ·
            refine ⟨69123075710306511694114061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46082050473537674462742707 69123075710306511694114061)
            ·
              refine ⟨25921153391364941885292773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69123075710306511694114061 25921153391364941885292773)
              ·
                refine ⟨4860216260880926603492395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25921153391364941885292773 4860216260880926603492395)
                ·
                  refine ⟨7290324391321389905238593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860216260880926603492395 7290324391321389905238593)
                  ·
                    refine ⟨5467743293491042428928945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290324391321389905238593 5467743293491042428928945)
                    ·
                      refine ⟨4100807470118281821696709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467743293491042428928945 4100807470118281821696709)
                      ·
                        rfl

theorem cell23_7986294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7986294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986294 prefixEnd_7986294 := by exact prefixLift 7986294
  have htrace : WordTrace (prefixWord ++ tailWord_7986294) baseStart_7986294 baseEnd_7986294 := by
    simpa [prefixWord, tailWord_7986294, baseEnd_7986294] using wordTrace_append hprefix tailTrace_7986294
  have hstable : (prefixWord ++ tailWord_7986294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986294).length < 2 ^ (prefixWord ++ tailWord_7986294).sum := by decide
  have hdescent : baseEnd_7986294 < baseStart_7986294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986336 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_7986336 : Nat := 118140960795 + 7986336 * 2 ^ 59
def prefixEnd_7986336 : Nat := 4983230072969 + 3 ^ 40 * 7986336 * 2
def baseEnd_7986336 : Nat := 4100829036305770657371515

theorem tailTrace_7986336 : CollatzResearch.WordTrace tailWord_7986336 prefixEnd_7986336 4100829036305770657371515 := by
  unfold tailWord_7986336
  simp only [CollatzResearch.WordTrace]
  refine ⟨145642801997438052221849431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194190402663250736295799241 145642801997438052221849431)
  ·
    refine ⟨218464202996157078332774147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145642801997438052221849431 218464202996157078332774147)
    ·
      refine ⟨327696304494235617499161221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218464202996157078332774147 327696304494235617499161221)
      ·
        refine ⟨61443057092669178281092729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327696304494235617499161221 61443057092669178281092729)
        ·
          refine ⟨46082292819501883710819547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61443057092669178281092729 46082292819501883710819547)
          ·
            refine ⟨69123439229252825566229321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46082292819501883710819547 69123439229252825566229321)
            ·
              refine ⟨51842579421939619174671991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69123439229252825566229321 51842579421939619174671991)
              ·
                refine ⟨77763869132909428762007987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51842579421939619174671991 77763869132909428762007987)
                ·
                  refine ⟨116645803699364143143011981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77763869132909428762007987 116645803699364143143011981)
                  ·
                    refine ⟨43742176387261553678629493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116645803699364143143011981 43742176387261553678629493)
                    ·
                      refine ⟨4100829036305770657371515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43742176387261553678629493 4100829036305770657371515)
                      ·
                        rfl

theorem cell23_7986336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_7986336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986336 prefixEnd_7986336 := by exact prefixLift 7986336
  have htrace : WordTrace (prefixWord ++ tailWord_7986336) baseStart_7986336 baseEnd_7986336 := by
    simpa [prefixWord, tailWord_7986336, baseEnd_7986336] using wordTrace_append hprefix tailTrace_7986336
  have hstable : (prefixWord ++ tailWord_7986336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986336).length < 2 ^ (prefixWord ++ tailWord_7986336).sum := by decide
  have hdescent : baseEnd_7986336 < baseStart_7986336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986343 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7986343 : Nat := 118140960795 + 7986343 * 2 ^ 59
def prefixEnd_7986343 : Nat := 4983230072969 + 3 ^ 40 * 7986343 * 2
def baseEnd_7986343 : Nat := 1366944210223450709994661

theorem tailTrace_7986343 : CollatzResearch.WordTrace tailWord_7986343 prefixEnd_7986343 1366944210223450709994661 := by
  unfold tailWord_7986343
  simp only [CollatzResearch.WordTrace]
  refine ⟨291285859305850744639203683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194190572870567163092802455 291285859305850744639203683)
  ·
    refine ⟨436928788958776116958805525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291285859305850744639203683 436928788958776116958805525)
    ·
      refine ⟨20481036982442630482444009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 436928788958776116958805525 20481036982442630482444009)
      ·
        refine ⟨15360777736831972861833007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20481036982442630482444009 15360777736831972861833007)
        ·
          refine ⟨23041166605247959292749511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15360777736831972861833007 23041166605247959292749511)
          ·
            refine ⟨34561749907871938939124267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23041166605247959292749511 34561749907871938939124267)
            ·
              refine ⟨51842624861807908408686401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34561749907871938939124267 51842624861807908408686401)
              ·
                refine ⟨38881968646355931306514801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51842624861807908408686401 38881968646355931306514801)
                ·
                  refine ⟨29161476484766948479886101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38881968646355931306514801 29161476484766948479886101)
                  ·
                    refine ⟨1366944210223450709994661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29161476484766948479886101 1366944210223450709994661)
                    ·
                      rfl

theorem cell23_7986343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7986343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986343 prefixEnd_7986343 := by exact prefixLift 7986343
  have htrace : WordTrace (prefixWord ++ tailWord_7986343) baseStart_7986343 baseEnd_7986343 := by
    simpa [prefixWord, tailWord_7986343, baseEnd_7986343] using wordTrace_append hprefix tailTrace_7986343
  have hstable : (prefixWord ++ tailWord_7986343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986343).length < 2 ^ (prefixWord ++ tailWord_7986343).sum := by decide
  have hdescent : baseEnd_7986343 < baseStart_7986343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986393 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 7, 2]
def baseStart_7986393 : Nat := 118140960795 + 7986393 * 2 ^ 59
def prefixEnd_7986393 : Nat := 4983230072969 + 3 ^ 40 * 7986393 * 2
def baseEnd_7986393 : Nat := 4100858304703076934358753

theorem tailTrace_7986393 : CollatzResearch.WordTrace tailWord_7986393 prefixEnd_7986393 4100858304703076934358753 := by
  unfold tailWord_7986393
  simp only [CollatzResearch.WordTrace]
  refine ⟨291287682955669603178523833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194191788637113068785682555 291287682955669603178523833)
  ·
    refine ⟨218465762216752202383892875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291287682955669603178523833 218465762216752202383892875)
    ·
      refine ⟨327698643325128303575839313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218465762216752202383892875 327698643325128303575839313)
      ·
        refine ⟨245773982493846227681879485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327698643325128303575839313 245773982493846227681879485)
        ·
          refine ⟨92165243435192335380704807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245773982493846227681879485 92165243435192335380704807)
          ·
            refine ⟨138247865152788503071057211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92165243435192335380704807 138247865152788503071057211)
            ·
              refine ⟨207371797729182754606585817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138247865152788503071057211 207371797729182754606585817)
              ·
                refine ⟨155528848296887065954939363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207371797729182754606585817 155528848296887065954939363)
                ·
                  refine ⟨233293272445330598932409045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155528848296887065954939363 233293272445330598932409045)
                  ·
                    refine ⟨5467811072937435912478337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233293272445330598932409045 5467811072937435912478337)
                    ·
                      refine ⟨4100858304703076934358753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467811072937435912478337 4100858304703076934358753)
                      ·
                        rfl

theorem cell23_7986393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_7986393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986393 prefixEnd_7986393 := by exact prefixLift 7986393
  have htrace : WordTrace (prefixWord ++ tailWord_7986393) baseStart_7986393 baseEnd_7986393 := by
    simpa [prefixWord, tailWord_7986393, baseEnd_7986393] using wordTrace_append hprefix tailTrace_7986393
  have hstable : (prefixWord ++ tailWord_7986393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986393).length < 2 ^ (prefixWord ++ tailWord_7986393).sum := by decide
  have hdescent : baseEnd_7986393 < baseStart_7986393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986407 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 7]
def baseStart_7986407 : Nat := 118140960795 + 7986407 * 2 ^ 59
def prefixEnd_7986407 : Nat := 4983230072969 + 3 ^ 40 * 7986407 * 2
def baseEnd_7986407 : Nat := 455651721492471097731521

theorem tailTrace_7986407 : CollatzResearch.WordTrace tailWord_7986407 prefixEnd_7986407 455651721492471097731521 := by
  unfold tailWord_7986407
  simp only [CollatzResearch.WordTrace]
  refine ⟨291288193577618883569533475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194192129051745922379688983 291288193577618883569533475)
  ·
    refine ⟨436932290366428325354300213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291288193577618883569533475 436932290366428325354300213)
    ·
      refine ⟨40962402221852655501965645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436932290366428325354300213 40962402221852655501965645)
      ·
        refine ⟨15360900833194745813237117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40962402221852655501965645 15360900833194745813237117)
        ·
          refine ⟨5760337812448029679963919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15360900833194745813237117 5760337812448029679963919)
          ·
            refine ⟨8640506718672044519945879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760337812448029679963919 8640506718672044519945879)
            ·
              refine ⟨12960760078008066779918819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640506718672044519945879 12960760078008066779918819)
              ·
                refine ⟨19441140117012100169878229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960760078008066779918819 19441140117012100169878229)
                ·
                  refine ⟨455651721492471097731521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19441140117012100169878229 455651721492471097731521)
                  ·
                    rfl

theorem cell23_7986407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 7].length) (baseStart_7986407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986407 prefixEnd_7986407 := by exact prefixLift 7986407
  have htrace : WordTrace (prefixWord ++ tailWord_7986407) baseStart_7986407 baseEnd_7986407 := by
    simpa [prefixWord, tailWord_7986407, baseEnd_7986407] using wordTrace_append hprefix tailTrace_7986407
  have hstable : (prefixWord ++ tailWord_7986407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986407).length < 2 ^ (prefixWord ++ tailWord_7986407).sum := by decide
  have hdescent : baseEnd_7986407 < baseStart_7986407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986413 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7986413 : Nat := 118140960795 + 7986413 * 2 ^ 59
def prefixEnd_7986413 : Nat := 4983230072969 + 3 ^ 40 * 7986413 * 2
def baseEnd_7986413 : Nat := 4100868574316166856108661

theorem tailTrace_7986413 : CollatzResearch.WordTrace tailWord_7986413 prefixEnd_7986413 4100868574316166856108661 := by
  unfold tailWord_7986413
  simp only [CollatzResearch.WordTrace]
  refine ⟨291288412415597146594251893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194192274943731431062834595 291288412415597146594251893)
  ·
    refine ⟨27308288663962232493211115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291288412415597146594251893 27308288663962232493211115)
    ·
      refine ⟨40962432995943348739816673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27308288663962232493211115 40962432995943348739816673)
      ·
        refine ⟨30721824746957511554862505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40962432995943348739816673 30721824746957511554862505)
        ·
          refine ⟨23041368560218133666146879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30721824746957511554862505 23041368560218133666146879)
          ·
            refine ⟨34562052840327200499220319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23041368560218133666146879 34562052840327200499220319)
            ·
              refine ⟨51843079260490800748830479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34562052840327200499220319 51843079260490800748830479)
              ·
                refine ⟨77764618890736201123245719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51843079260490800748830479 77764618890736201123245719)
                ·
                  refine ⟨116646928336104301684868579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77764618890736201123245719 116646928336104301684868579)
                  ·
                    refine ⟨174970392504156452527302869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116646928336104301684868579 174970392504156452527302869)
                    ·
                      refine ⟨4100868574316166856108661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174970392504156452527302869 4100868574316166856108661)
                      ·
                        rfl

theorem cell23_7986413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7986413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986413 prefixEnd_7986413 := by exact prefixLift 7986413
  have htrace : WordTrace (prefixWord ++ tailWord_7986413) baseStart_7986413 baseEnd_7986413 := by
    simpa [prefixWord, tailWord_7986413, baseEnd_7986413] using wordTrace_append hprefix tailTrace_7986413
  have hstable : (prefixWord ++ tailWord_7986413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986413).length < 2 ^ (prefixWord ++ tailWord_7986413).sum := by decide
  have hdescent : baseEnd_7986413 < baseStart_7986413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986418 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_7986418 : Nat := 118140960795 + 7986418 * 2 ^ 59
def prefixEnd_7986418 : Nat := 4983230072969 + 3 ^ 40 * 7986418 * 2
def baseEnd_7986418 : Nat := 4100871141719439336546139

theorem tailTrace_7986418 : CollatzResearch.WordTrace tailWord_7986418 prefixEnd_7986418 4100871141719439336546139 := by
  unfold tailWord_7986418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72822148695144758112045977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194192396520386021632122605 72822148695144758112045977)
  ·
    refine ⟨54616611521358568584034483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72822148695144758112045977 54616611521358568584034483)
    ·
      refine ⟨81924917282037852876051725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54616611521358568584034483 81924917282037852876051725)
      ·
        refine ⟨30721843980764194828519397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81924917282037852876051725 30721843980764194828519397)
        ·
          refine ⟨5760345746393286530347387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30721843980764194828519397 5760345746393286530347387)
          ·
            refine ⟨8640518619589929795521081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760345746393286530347387 8640518619589929795521081)
            ·
              refine ⟨6480388964692447346640811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640518619589929795521081 6480388964692447346640811)
              ·
                refine ⟨9720583447038671019961217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480388964692447346640811 9720583447038671019961217)
                ·
                  refine ⟨7290437585279003264970913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9720583447038671019961217 7290437585279003264970913)
                  ·
                    refine ⟨5467828188959252448728185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290437585279003264970913 5467828188959252448728185)
                    ·
                      refine ⟨4100871141719439336546139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5467828188959252448728185 4100871141719439336546139)
                      ·
                        rfl

theorem cell23_7986418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_7986418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986418 prefixEnd_7986418 := by exact prefixLift 7986418
  have htrace : WordTrace (prefixWord ++ tailWord_7986418) baseStart_7986418 baseEnd_7986418 := by
    simpa [prefixWord, tailWord_7986418, baseEnd_7986418] using wordTrace_append hprefix tailTrace_7986418
  have hstable : (prefixWord ++ tailWord_7986418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986418).length < 2 ^ (prefixWord ++ tailWord_7986418).sum := by decide
  have hdescent : baseEnd_7986418 < baseStart_7986418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986460 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7986460 : Nat := 118140960795 + 7986460 * 2 ^ 59
def prefixEnd_7986460 : Nat := 4983230072969 + 3 ^ 40 * 7986460 * 2
def baseEnd_7986460 : Nat := 4100892707906928172220945

theorem tailTrace_7986460 : CollatzResearch.WordTrace tailWord_7986460 prefixEnd_7986460 4100892707906928172220945 := by
  unfold tailWord_7986460
  simp only [CollatzResearch.WordTrace]
  refine ⟨145645063323213436810606417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194193417764284582414141889 145645063323213436810606417)
  ·
    refine ⟨109233797492410077607954813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145645063323213436810606417 109233797492410077607954813)
    ·
      refine ⟨40962674059653779102983055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109233797492410077607954813 40962674059653779102983055)
      ·
        refine ⟨61444011089480668654474583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40962674059653779102983055 61444011089480668654474583)
        ·
          refine ⟨92166016634221002981711875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61444011089480668654474583 92166016634221002981711875)
          ·
            refine ⟨138249024951331504472567813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92166016634221002981711875 138249024951331504472567813)
            ·
              refine ⟨25921692178374657088606465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138249024951331504472567813 25921692178374657088606465)
              ·
                refine ⟨19441269133780992816454849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25921692178374657088606465 19441269133780992816454849)
                ·
                  refine ⟨14580951850335744612341137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19441269133780992816454849 14580951850335744612341137)
                  ·
                    refine ⟨10935713887751808459255853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14580951850335744612341137 10935713887751808459255853)
                    ·
                      refine ⟨4100892707906928172220945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10935713887751808459255853 4100892707906928172220945)
                      ·
                        rfl

theorem cell23_7986460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7986460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986460 prefixEnd_7986460 := by exact prefixLift 7986460
  have htrace : WordTrace (prefixWord ++ tailWord_7986460) baseStart_7986460 baseEnd_7986460 := by
    simpa [prefixWord, tailWord_7986460, baseEnd_7986460] using wordTrace_append hprefix tailTrace_7986460
  have hstable : (prefixWord ++ tailWord_7986460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986460).length < 2 ^ (prefixWord ++ tailWord_7986460).sum := by decide
  have hdescent : baseEnd_7986460 < baseStart_7986460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986467 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 1, 4]
def baseStart_7986467 : Nat := 118140960795 + 7986467 * 2 ^ 59
def prefixEnd_7986467 : Nat := 4983230072969 + 3 ^ 40 * 7986467 * 2
def baseEnd_7986467 : Nat := 1366965434090503214944471

theorem tailTrace_7986467 : CollatzResearch.WordTrace tailWord_7986467 prefixEnd_7986467 1366965434090503214944471 := by
  unfold tailWord_7986467
  simp only [CollatzResearch.WordTrace]
  refine ⟨291290381957401513816717655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194193587971601009211145103 291290381957401513816717655)
  ·
    refine ⟨436935572936102270725076483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291290381957401513816717655 436935572936102270725076483)
    ·
      refine ⟨655403359404153406087614725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436935572936102270725076483 655403359404153406087614725)
      ·
        refine ⟨122888129888278763641427761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655403359404153406087614725 122888129888278763641427761)
        ·
          refine ⟨92166097416209072731070821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122888129888278763641427761 92166097416209072731070821)
          ·
            refine ⟨17281143265539201137075779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92166097416209072731070821 17281143265539201137075779)
            ·
              refine ⟨25921714898308801705613669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17281143265539201137075779 25921714898308801705613669)
              ·
                refine ⟨4860321543432900319802563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25921714898308801705613669 4860321543432900319802563)
                ·
                  refine ⟨7290482315149350479703845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860321543432900319802563 7290482315149350479703845)
                  ·
                    refine ⟨1366965434090503214944471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290482315149350479703845 1366965434090503214944471)
                    ·
                      rfl

theorem cell23_7986467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 4].length) (baseStart_7986467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986467 prefixEnd_7986467 := by exact prefixLift 7986467
  have htrace : WordTrace (prefixWord ++ tailWord_7986467) baseStart_7986467 baseEnd_7986467 := by
    simpa [prefixWord, tailWord_7986467, baseEnd_7986467] using wordTrace_append hprefix tailTrace_7986467
  have hstable : (prefixWord ++ tailWord_7986467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986467).length < 2 ^ (prefixWord ++ tailWord_7986467).sum := by decide
  have hdescent : baseEnd_7986467 < baseStart_7986467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986510 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_7986510 : Nat := 118140960795 + 7986510 * 2 ^ 59
def prefixEnd_7986510 : Nat := 4983230072969 + 3 ^ 40 * 7986510 * 2
def baseEnd_7986510 : Nat := 1366972793979884325531905

theorem tailTrace_7986510 : CollatzResearch.WordTrace tailWord_7986510 prefixEnd_7986510 1366972793979884325531905 := by
  unfold tailWord_7986510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36411493787030716520066623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194194633530830488107021989 36411493787030716520066623)
  ·
    refine ⟨54617240680546074780099935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36411493787030716520066623 54617240680546074780099935)
    ·
      refine ⟨81925861020819112170149903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54617240680546074780099935 81925861020819112170149903)
      ·
        refine ⟨122888791531228668255224855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81925861020819112170149903 122888791531228668255224855)
        ·
          refine ⟨184333187296843002382837283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122888791531228668255224855 184333187296843002382837283)
          ·
            refine ⟨276499780945264503574255925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184333187296843002382837283 276499780945264503574255925)
            ·
              refine ⟨25921854463618547210086493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276499780945264503574255925 25921854463618547210086493)
              ·
                refine ⟨9720695423856955203782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25921854463618547210086493 9720695423856955203782435)
                ·
                  refine ⟨14581043135785432805673653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720695423856955203782435 14581043135785432805673653)
                  ·
                    refine ⟨1366972793979884325531905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14581043135785432805673653 1366972793979884325531905)
                    ·
                      rfl

theorem cell23_7986510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_7986510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986510 prefixEnd_7986510 := by exact prefixLift 7986510
  have htrace : WordTrace (prefixWord ++ tailWord_7986510) baseStart_7986510 baseEnd_7986510 := by
    simpa [prefixWord, tailWord_7986510, baseEnd_7986510] using wordTrace_append hprefix tailTrace_7986510
  have hstable : (prefixWord ++ tailWord_7986510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986510).length < 2 ^ (prefixWord ++ tailWord_7986510).sum := by decide
  have hdescent : baseEnd_7986510 < baseStart_7986510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986518 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7986518 : Nat := 118140960795 + 7986518 * 2 ^ 59
def prefixEnd_7986518 : Nat := 4983230072969 + 3 ^ 40 * 7986518 * 2
def baseEnd_7986518 : Nat := 1366974163261629648431893

theorem tailTrace_7986518 : CollatzResearch.WordTrace tailWord_7986518 prefixEnd_7986518 1366974163261629648431893 := by
  unfold tailWord_7986518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18205765130013546845426513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194194828053477833017882805 18205765130013546845426513)
  ·
    refine ⟨13654323847510160134069885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18205765130013546845426513 13654323847510160134069885)
    ·
      refine ⟨5120371442816310050276207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13654323847510160134069885 5120371442816310050276207)
      ·
        refine ⟨7680557164224465075414311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120371442816310050276207 7680557164224465075414311)
        ·
          refine ⟨11520835746336697613121467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680557164224465075414311 11520835746336697613121467)
          ·
            refine ⟨17281253619505046419682201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520835746336697613121467 17281253619505046419682201)
            ·
              refine ⟨12960940214628784814761651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17281253619505046419682201 12960940214628784814761651)
              ·
                refine ⟨19441410321943177222142477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960940214628784814761651 19441410321943177222142477)
                ·
                  refine ⟨7290528870728691458303429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19441410321943177222142477 7290528870728691458303429)
                  ·
                    refine ⟨1366974163261629648431893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290528870728691458303429 1366974163261629648431893)
                    ·
                      rfl

theorem cell23_7986518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7986518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986518 prefixEnd_7986518 := by exact prefixLift 7986518
  have htrace : WordTrace (prefixWord ++ tailWord_7986518) baseStart_7986518 baseEnd_7986518 := by
    simpa [prefixWord, tailWord_7986518, baseEnd_7986518] using wordTrace_append hprefix tailTrace_7986518
  have hstable : (prefixWord ++ tailWord_7986518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986518).length < 2 ^ (prefixWord ++ tailWord_7986518).sum := by decide
  have hdescent : baseEnd_7986518 < baseStart_7986518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986540 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_7986540 : Nat := 118140960795 + 7986540 * 2 ^ 59
def prefixEnd_7986540 : Nat := 4983230072969 + 3 ^ 40 * 7986540 * 2
def baseEnd_7986540 : Nat := 1366977928786429286406859

theorem tailTrace_7986540 : CollatzResearch.WordTrace tailWord_7986540 prefixEnd_7986540 1366977928786429286406859 := by
  unfold tailWord_7986540
  simp only [CollatzResearch.WordTrace]
  refine ⟨145646522243068523642062537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194195362990758031522750049 145646522243068523642062537)
  ·
    refine ⟨109234891682301392731546903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145646522243068523642062537 109234891682301392731546903)
    ·
      refine ⟨163852337523452089097320355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109234891682301392731546903 163852337523452089097320355)
      ·
        refine ⟨245778506285178133645980533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163852337523452089097320355 245778506285178133645980533)
        ·
          refine ⟨23041734964235450029310675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245778506285178133645980533 23041734964235450029310675)
          ·
            refine ⟨34562602446353175043966013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23041734964235450029310675 34562602446353175043966013)
            ·
              refine ⟨12960975917382440641487255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34562602446353175043966013 12960975917382440641487255)
              ·
                refine ⟨19441463876073660962230883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960975917382440641487255 19441463876073660962230883)
                ·
                  refine ⟨29162195814110491443346325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441463876073660962230883 29162195814110491443346325)
                  ·
                    refine ⟨1366977928786429286406859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29162195814110491443346325 1366977928786429286406859)
                    ·
                      rfl

theorem cell23_7986540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_7986540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986540 prefixEnd_7986540 := by exact prefixLift 7986540
  have htrace : WordTrace (prefixWord ++ tailWord_7986540) baseStart_7986540 baseEnd_7986540 := by
    simpa [prefixWord, tailWord_7986540, baseEnd_7986540] using wordTrace_append hprefix tailTrace_7986540
  have hstable : (prefixWord ++ tailWord_7986540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986540).length < 2 ^ (prefixWord ++ tailWord_7986540).sum := by decide
  have hdescent : baseEnd_7986540 < baseStart_7986540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986543 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_7986543 : Nat := 118140960795 + 7986543 * 2 ^ 59
def prefixEnd_7986543 : Nat := 4983230072969 + 3 ^ 40 * 7986543 * 2
def baseEnd_7986543 : Nat := 4100935326801251347483063

theorem tailTrace_7986543 : CollatzResearch.WordTrace tailWord_7986543 prefixEnd_7986543 4100935326801251347483063 := by
  unfold tailWord_7986543
  simp only [CollatzResearch.WordTrace]
  refine ⟨291293153905126178796484283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194195435936750785864322855 291293153905126178796484283)
  ·
    refine ⟨436939730857689268194726425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291293153905126178796484283 436939730857689268194726425)
    ·
      refine ⟨327704798143266951146044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436939730857689268194726425 327704798143266951146044819)
      ·
        refine ⟨491557197214900426719067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327704798143266951146044819 491557197214900426719067229)
        ·
          refine ⟨184333948955587660019650211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491557197214900426719067229 184333948955587660019650211)
          ·
            refine ⟨276500923433381490029475317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184333948955587660019650211 276500923433381490029475317)
            ·
              refine ⟨25921961571879514690263311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276500923433381490029475317 25921961571879514690263311)
              ·
                refine ⟨38882942357819272035394967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25921961571879514690263311 38882942357819272035394967)
                ·
                  refine ⟨58324413536728908053092451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38882942357819272035394967 58324413536728908053092451)
                  ·
                    refine ⟨87486620305093362079638677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58324413536728908053092451 87486620305093362079638677)
                    ·
                      refine ⟨4100935326801251347483063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87486620305093362079638677 4100935326801251347483063)
                      ·
                        rfl

theorem cell23_7986543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_7986543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986543 prefixEnd_7986543 := by exact prefixLift 7986543
  have htrace : WordTrace (prefixWord ++ tailWord_7986543) baseStart_7986543 baseEnd_7986543 := by
    simpa [prefixWord, tailWord_7986543, baseEnd_7986543] using wordTrace_append hprefix tailTrace_7986543
  have hstable : (prefixWord ++ tailWord_7986543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986543).length < 2 ^ (prefixWord ++ tailWord_7986543).sum := by decide
  have hdescent : baseEnd_7986543 < baseStart_7986543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986567 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_7986567 : Nat := 118140960795 + 7986567 * 2 ^ 59
def prefixEnd_7986567 : Nat := 4983230072969 + 3 ^ 40 * 7986567 * 2
def baseEnd_7986567 : Nat := 4100947650336959253582953

theorem tailTrace_7986567 : CollatzResearch.WordTrace tailWord_7986567 prefixEnd_7986567 4100947650336959253582953 := by
  unfold tailWord_7986567
  simp only [CollatzResearch.WordTrace]
  refine ⟨291294029257039230895357955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194196019504692820596905303 291294029257039230895357955)
  ·
    refine ⟨436941043885558846343036933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291294029257039230895357955 436941043885558846343036933)
    ·
      refine ⟨81926445728542283689319425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 436941043885558846343036933 81926445728542283689319425)
      ·
        refine ⟨61444834296406712766989569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81926445728542283689319425 61444834296406712766989569)
        ·
          refine ⟨46083625722305034575242177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61444834296406712766989569 46083625722305034575242177)
          ·
            refine ⟨34562719291728775931431633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46083625722305034575242177 34562719291728775931431633)
            ·
              refine ⟨25922039468796581948573725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34562719291728775931431633 25922039468796581948573725)
              ·
                refine ⟨9720764800798718230715147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25922039468796581948573725 9720764800798718230715147)
                ·
                  refine ⟨14581147201198077346072721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720764800798718230715147 14581147201198077346072721)
                  ·
                    refine ⟨10935860400898558009554541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14581147201198077346072721 10935860400898558009554541)
                    ·
                      refine ⟨4100947650336959253582953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10935860400898558009554541 4100947650336959253582953)
                      ·
                        rfl

theorem cell23_7986567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_7986567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986567 prefixEnd_7986567 := by exact prefixLift 7986567
  have htrace : WordTrace (prefixWord ++ tailWord_7986567) baseStart_7986567 baseEnd_7986567 := by
    simpa [prefixWord, tailWord_7986567, baseEnd_7986567] using wordTrace_append hprefix tailTrace_7986567
  have hstable : (prefixWord ++ tailWord_7986567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986567).length < 2 ^ (prefixWord ++ tailWord_7986567).sum := by decide
  have hdescent : baseEnd_7986567 < baseStart_7986567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986583 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 7]
def baseStart_7986583 : Nat := 118140960795 + 7986583 * 2 ^ 59
def prefixEnd_7986583 : Nat := 4983230072969 + 3 ^ 40 * 7986583 * 2
def baseEnd_7986583 : Nat := 1366985288675810396994293

theorem tailTrace_7986583 : CollatzResearch.WordTrace tailWord_7986583 prefixEnd_7986583 1366985288675810396994293 := by
  unfold tailWord_7986583
  simp only [CollatzResearch.WordTrace]
  refine ⟨291294612824981265627940403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194196408549987510418626935 291294612824981265627940403)
  ·
    refine ⟨436941919237471898441910605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291294612824981265627940403 436941919237471898441910605)
    ·
      refine ⟨163853219714051961915716477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436941919237471898441910605 163853219714051961915716477)
      ·
        refine ⟨61444957392769485718393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163853219714051961915716477 61444957392769485718393679)
        ·
          refine ⟨92167436089154228577590519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61444957392769485718393679 92167436089154228577590519)
          ·
            refine ⟨138251154133731342866385779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92167436089154228577590519 138251154133731342866385779)
            ·
              refine ⟨207376731200597014299578669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138251154133731342866385779 207376731200597014299578669)
              ·
                refine ⟨77766274200223880362342001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207376731200597014299578669 77766274200223880362342001)
                ·
                  refine ⟨58324705650167910271756501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77766274200223880362342001 58324705650167910271756501)
                  ·
                    refine ⟨1366985288675810396994293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58324705650167910271756501 1366985288675810396994293)
                    ·
                      rfl

theorem cell23_7986583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_7986583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986583 prefixEnd_7986583 := by exact prefixLift 7986583
  have htrace : WordTrace (prefixWord ++ tailWord_7986583) baseStart_7986583 baseEnd_7986583 := by
    simpa [prefixWord, tailWord_7986583, baseEnd_7986583] using wordTrace_append hprefix tailTrace_7986583
  have hstable : (prefixWord ++ tailWord_7986583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986583).length < 2 ^ (prefixWord ++ tailWord_7986583).sum := by decide
  have hdescent : baseEnd_7986583 < baseStart_7986583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986626 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7986626 : Nat := 118140960795 + 7986626 * 2 ^ 59
def prefixEnd_7986626 : Nat := 4983230072969 + 3 ^ 40 * 7986626 * 2
def baseEnd_7986626 : Nat := 4100977945695574522745183

theorem tailTrace_7986626 : CollatzResearch.WordTrace tailWord_7986626 prefixEnd_7986626 4100977945695574522745183 := by
  unfold tailWord_7986626
  simp only [CollatzResearch.WordTrace]
  refine ⟨72824045290956370992938933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194197454109216989314503821 72824045290956370992938933)
  ·
    refine ⟨6827254246027159780588025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72824045290956370992938933 6827254246027159780588025)
    ·
      refine ⟨5120440684520369835441019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6827254246027159780588025 5120440684520369835441019)
      ·
        refine ⟨7680661026780554753161529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120440684520369835441019 7680661026780554753161529)
        ·
          refine ⟨5760495770085416064871147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7680661026780554753161529 5760495770085416064871147)
          ·
            refine ⟨8640743655128124097306721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760495770085416064871147 8640743655128124097306721)
            ·
              refine ⟨6480557741346093072980041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640743655128124097306721 6480557741346093072980041)
              ·
                refine ⟨4860418306009569804735031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480557741346093072980041 4860418306009569804735031)
                ·
                  refine ⟨7290627459014354707102547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860418306009569804735031 7290627459014354707102547)
                  ·
                    refine ⟨10935941188521532060653821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290627459014354707102547 10935941188521532060653821)
                    ·
                      refine ⟨4100977945695574522745183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10935941188521532060653821 4100977945695574522745183)
                      ·
                        rfl

theorem cell23_7986626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7986626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986626 prefixEnd_7986626 := by exact prefixLift 7986626
  have htrace : WordTrace (prefixWord ++ tailWord_7986626) baseStart_7986626 baseEnd_7986626 := by
    simpa [prefixWord, tailWord_7986626, baseEnd_7986626] using wordTrace_append hprefix tailTrace_7986626
  have hstable : (prefixWord ++ tailWord_7986626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986626).length < 2 ^ (prefixWord ++ tailWord_7986626).sum := by decide
  have hdescent : baseEnd_7986626 < baseStart_7986626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986633 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_7986633 : Nat := 118140960795 + 7986633 * 2 ^ 59
def prefixEnd_7986633 : Nat := 4983230072969 + 3 ^ 40 * 7986633 * 2
def baseEnd_7986633 : Nat := 4100981540060155995357649

theorem tailTrace_7986633 : CollatzResearch.WordTrace tailWord_7986633 prefixEnd_7986633 4100981540060155995357649 := by
  unfold tailWord_7986633
  simp only [CollatzResearch.WordTrace]
  refine ⟨291296436474800124167260553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194197624316533416111507035 291296436474800124167260553)
  ·
    refine ⟨218472327356100093125445415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291296436474800124167260553 218472327356100093125445415)
    ·
      refine ⟨327708491034150139688168123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218472327356100093125445415 327708491034150139688168123)
      ·
        refine ⟨491562736551225209532252185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327708491034150139688168123 491562736551225209532252185)
        ·
          refine ⟨368672052413418907149189139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491562736551225209532252185 368672052413418907149189139)
          ·
            refine ⟨553008078620128360723783709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368672052413418907149189139 553008078620128360723783709)
            ·
              refine ⟨207378029482548135271418891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553008078620128360723783709 207378029482548135271418891)
              ·
                refine ⟨311067044223822202907128337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207378029482548135271418891 311067044223822202907128337)
                ·
                  refine ⟨233300283167866652180346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311067044223822202907128337 233300283167866652180346253)
                  ·
                    refine ⟨87487606187949994567629845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233300283167866652180346253 87487606187949994567629845)
                    ·
                      refine ⟨4100981540060155995357649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87487606187949994567629845 4100981540060155995357649)
                      ·
                        rfl

theorem cell23_7986633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_7986633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986633 prefixEnd_7986633 := by exact prefixLift 7986633
  have htrace : WordTrace (prefixWord ++ tailWord_7986633) baseStart_7986633 baseEnd_7986633 := by
    simpa [prefixWord, tailWord_7986633, baseEnd_7986633] using wordTrace_append hprefix tailTrace_7986633
  have hstable : (prefixWord ++ tailWord_7986633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986633).length < 2 ^ (prefixWord ++ tailWord_7986633).sum := by decide
  have hdescent : baseEnd_7986633 < baseStart_7986633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986650 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_7986650 : Nat := 118140960795 + 7986650 * 2 ^ 59
def prefixEnd_7986650 : Nat := 4983230072969 + 3 ^ 40 * 7986650 * 2
def baseEnd_7986650 : Nat := 4100990269231282428845071

theorem tailTrace_7986650 : CollatzResearch.WordTrace tailWord_7986650 prefixEnd_7986650 4100990269231282428845071 := by
  unfold tailWord_7986650
  simp only [CollatzResearch.WordTrace]
  refine ⟨72824264128934634017657351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194198037677159024047086269 72824264128934634017657351)
  ·
    refine ⟨109236396193401951026486027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72824264128934634017657351 109236396193401951026486027)
    ·
      refine ⟨163854594290102926539729041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109236396193401951026486027 163854594290102926539729041)
      ·
        refine ⟨122890945717577194904796781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163854594290102926539729041 122890945717577194904796781)
        ·
          refine ⟨46084104644091448089298793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122890945717577194904796781 46084104644091448089298793)
          ·
            refine ⟨34563078483068586066974095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46084104644091448089298793 34563078483068586066974095)
            ·
              refine ⟨51844617724602879100461143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34563078483068586066974095 51844617724602879100461143)
              ·
                refine ⟨77766926586904318650691715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51844617724602879100461143 77766926586904318650691715)
                ·
                  refine ⟨116650389880356477976037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77766926586904318650691715 116650389880356477976037573)
                  ·
                    refine ⟨21871948102566839620507045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116650389880356477976037573 21871948102566839620507045)
                    ·
                      refine ⟨4100990269231282428845071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21871948102566839620507045 4100990269231282428845071)
                      ·
                        rfl

theorem cell23_7986650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_7986650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986650 prefixEnd_7986650 := by exact prefixLift 7986650
  have htrace : WordTrace (prefixWord ++ tailWord_7986650) baseStart_7986650 baseEnd_7986650 := by
    simpa [prefixWord, tailWord_7986650, baseEnd_7986650] using wordTrace_append hprefix tailTrace_7986650
  have hstable : (prefixWord ++ tailWord_7986650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986650).length < 2 ^ (prefixWord ++ tailWord_7986650).sum := by decide
  have hdescent : baseEnd_7986650 < baseStart_7986650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986728 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 5]
def baseStart_7986728 : Nat := 118140960795 + 7986728 * 2 ^ 59
def prefixEnd_7986728 : Nat := 4983230072969 + 3 ^ 40 * 7986728 * 2
def baseEnd_7986728 : Nat := 455670035635814791518857

theorem tailTrace_7986728 : CollatzResearch.WordTrace tailWord_7986728 prefixEnd_7986728 455670035635814791518857 := by
  unfold tailWord_7986728
  simp only [CollatzResearch.WordTrace]
  refine ⟨145649950704727977695984419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194199934272970636927979225 145649950704727977695984419)
  ·
    refine ⟨218474926057091966543976629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145649950704727977695984419 218474926057091966543976629)
    ·
      refine ⟨20482024317852371863497809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218474926057091966543976629 20482024317852371863497809)
      ·
        refine ⟨15361518238389278897623357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20482024317852371863497809 15361518238389278897623357)
        ·
          refine ⟨5760569339395979586608759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15361518238389278897623357 5760569339395979586608759)
          ·
            refine ⟨8640854009093969379913139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760569339395979586608759 8640854009093969379913139)
            ·
              refine ⟨12961281013640954069869709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640854009093969379913139 12961281013640954069869709)
              ·
                refine ⟨4860480380115357776201141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12961281013640954069869709 4860480380115357776201141)
                ·
                  refine ⟨455670035635814791518857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860480380115357776201141 455670035635814791518857)
                  ·
                    rfl

theorem cell23_7986728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 5].length) (baseStart_7986728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986728 prefixEnd_7986728 := by exact prefixLift 7986728
  have htrace : WordTrace (prefixWord ++ tailWord_7986728) baseStart_7986728 baseEnd_7986728 := by
    simpa [prefixWord, tailWord_7986728, baseEnd_7986728] using wordTrace_append hprefix tailTrace_7986728
  have hstable : (prefixWord ++ tailWord_7986728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986728).length < 2 ^ (prefixWord ++ tailWord_7986728).sum := by decide
  have hdescent : baseEnd_7986728 < baseStart_7986728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986805 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7986805 : Nat := 118140960795 + 7986805 * 2 ^ 59
def prefixEnd_7986805 : Nat := 4983230072969 + 3 ^ 40 * 7986805 * 2
def baseEnd_7986805 : Nat := 1367023286244243107468953

theorem tailTrace_7986805 : CollatzResearch.WordTrace tailWord_7986805 prefixEnd_7986805 1367023286244243107468953 := by
  unfold tailWord_7986805
  simp only [CollatzResearch.WordTrace]
  refine ⟨291302709830176997542521869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194201806553451331695014579 291302709830176997542521869)
  ·
    refine ⟨109238516186316374078445701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291302709830176997542521869 109238516186316374078445701)
    ·
      refine ⟨20482221784934320139708569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109238516186316374078445701 20482221784934320139708569)
      ·
        refine ⟨15361666338700740104781427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20482221784934320139708569 15361666338700740104781427)
        ·
          refine ⟨23042499508051110157172141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15361666338700740104781427 23042499508051110157172141)
          ·
            refine ⟨8640937315519166308939553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23042499508051110157172141 8640937315519166308939553)
            ·
              refine ⟨6480702986639374731704665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8640937315519166308939553 6480702986639374731704665)
              ·
                refine ⟨4860527239979531048778499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480702986639374731704665 4860527239979531048778499)
                ·
                  refine ⟨7290790859969296573167749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860527239979531048778499 7290790859969296573167749)
                  ·
                    refine ⟨1367023286244243107468953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290790859969296573167749 1367023286244243107468953)
                    ·
                      rfl

theorem cell23_7986805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7986805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986805 prefixEnd_7986805 := by exact prefixLift 7986805
  have htrace : WordTrace (prefixWord ++ tailWord_7986805) baseStart_7986805 baseEnd_7986805 := by
    simpa [prefixWord, tailWord_7986805, baseEnd_7986805] using wordTrace_append hprefix tailTrace_7986805
  have hstable : (prefixWord ++ tailWord_7986805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986805).length < 2 ^ (prefixWord ++ tailWord_7986805).sum := by decide
  have hdescent : baseEnd_7986805 < baseStart_7986805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986811 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 1, 1, 3]
def baseStart_7986811 : Nat := 118140960795 + 7986811 * 2 ^ 59
def prefixEnd_7986811 : Nat := 4983230072969 + 3 ^ 40 * 7986811 * 2
def baseEnd_7986811 : Nat := 4101072939616656298931831

theorem tailTrace_7986811 : CollatzResearch.WordTrace tailWord_7986811 prefixEnd_7986811 4101072939616656298931831 := by
  unfold tailWord_7986811
  simp only [CollatzResearch.WordTrace]
  refine ⟨291302928668155260567240287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194201952445436840378160191 291302928668155260567240287)
  ·
    refine ⟨436954393002232890850860431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291302928668155260567240287 436954393002232890850860431)
    ·
      refine ⟨655431589503349336276290647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436954393002232890850860431 655431589503349336276290647)
      ·
        refine ⟨983147384255024004414435971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655431589503349336276290647 983147384255024004414435971)
        ·
          refine ⟨1474721076382536006621653957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983147384255024004414435971 1474721076382536006621653957)
          ·
            refine ⟨276510201821725501241560117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1474721076382536006621653957 276510201821725501241560117)
            ·
              refine ⟨25922831420786765741396261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276510201821725501241560117 25922831420786765741396261)
              ·
                refine ⟨4860530891397518576511799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25922831420786765741396261 4860530891397518576511799)
                ·
                  refine ⟨7290796337096277864767699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860530891397518576511799 7290796337096277864767699)
                  ·
                    refine ⟨10936194505644416797151549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290796337096277864767699 10936194505644416797151549)
                    ·
                      refine ⟨4101072939616656298931831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10936194505644416797151549 4101072939616656298931831)
                      ·
                        rfl

theorem cell23_7986811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 1, 3].length) (baseStart_7986811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986811 prefixEnd_7986811 := by exact prefixLift 7986811
  have htrace : WordTrace (prefixWord ++ tailWord_7986811) baseStart_7986811 baseEnd_7986811 := by
    simpa [prefixWord, tailWord_7986811, baseEnd_7986811] using wordTrace_append hprefix tailTrace_7986811
  have hstable : (prefixWord ++ tailWord_7986811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986811).length < 2 ^ (prefixWord ++ tailWord_7986811).sum := by decide
  have hdescent : baseEnd_7986811 < baseStart_7986811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986827 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 6]
def baseStart_7986827 : Nat := 118140960795 + 7986827 * 2 ^ 59
def prefixEnd_7986827 : Nat := 4983230072969 + 3 ^ 40 * 7986827 * 2
def baseEnd_7986827 : Nat := 1367027051769042745443919

theorem tailTrace_7986827 : CollatzResearch.WordTrace tailWord_7986827 prefixEnd_7986827 1367027051769042745443919 := by
  unfold tailWord_7986827
  simp only [CollatzResearch.WordTrace]
  refine ⟨291303512236097295299822735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194202341490731530199881823 291303512236097295299822735)
  ·
    refine ⟨436955268354145942949734103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291303512236097295299822735 436955268354145942949734103)
    ·
      refine ⟨655432902531218914424601155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436955268354145942949734103 655432902531218914424601155)
      ·
        refine ⟨983149353796828371636901733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655432902531218914424601155 983149353796828371636901733)
        ·
          refine ⟨184340503836905319681919075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 983149353796828371636901733 184340503836905319681919075)
          ·
            refine ⟨276510755755357979522878613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184340503836905319681919075 276510755755357979522878613)
            ·
              refine ⟨12961441676032405290134935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276510755755357979522878613 12961441676032405290134935)
              ·
                refine ⟨19442162514048607935202403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961441676032405290134935 19442162514048607935202403)
                ·
                  refine ⟨29163243771072911902803605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19442162514048607935202403 29163243771072911902803605)
                  ·
                    refine ⟨1367027051769042745443919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29163243771072911902803605 1367027051769042745443919)
                    ·
                      rfl

theorem cell23_7986827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].length) (baseStart_7986827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986827 prefixEnd_7986827 := by exact prefixLift 7986827
  have htrace : WordTrace (prefixWord ++ tailWord_7986827) baseStart_7986827 baseEnd_7986827 := by
    simpa [prefixWord, tailWord_7986827, baseEnd_7986827] using wordTrace_append hprefix tailTrace_7986827
  have hstable : (prefixWord ++ tailWord_7986827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986827).length < 2 ^ (prefixWord ++ tailWord_7986827).sum := by decide
  have hdescent : baseEnd_7986827 < baseStart_7986827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986878 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7986878 : Nat := 118140960795 + 7986878 * 2 ^ 59
def prefixEnd_7986878 : Nat := 4983230072969 + 3 ^ 40 * 7986878 * 2
def baseEnd_7986878 : Nat := 1367035780940169178931341

theorem tailTrace_7986878 : CollatzResearch.WordTrace tailWord_7986878 prefixEnd_7986878 1367035780940169178931341 := by
  unfold tailWord_7986878
  simp only [CollatzResearch.WordTrace]
  refine ⟨36413171544864066376241161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194203581572608354006619525 36413171544864066376241161)
  ·
    refine ⟨27309878658648049782180871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36413171544864066376241161 27309878658648049782180871)
    ·
      refine ⟨40964817987972074673271307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27309878658648049782180871 40964817987972074673271307)
      ·
        refine ⟨61447226981958112009906961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40964817987972074673271307 61447226981958112009906961)
        ·
          refine ⟨46085420236468584007430221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61447226981958112009906961 46085420236468584007430221)
          ·
            refine ⟨17282032588675719002786333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46085420236468584007430221 17282032588675719002786333)
            ·
              refine ⟨6480762220753394626044875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282032588675719002786333 6480762220753394626044875)
              ·
                refine ⟨9721143331130091939067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480762220753394626044875 9721143331130091939067313)
                ·
                  refine ⟨7290857498347568954300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721143331130091939067313 7290857498347568954300485)
                  ·
                    refine ⟨1367035780940169178931341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290857498347568954300485 1367035780940169178931341)
                    ·
                      rfl

theorem cell23_7986878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7986878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986878 prefixEnd_7986878 := by exact prefixLift 7986878
  have htrace : WordTrace (prefixWord ++ tailWord_7986878) baseStart_7986878 baseEnd_7986878 := by
    simpa [prefixWord, tailWord_7986878, baseEnd_7986878] using wordTrace_append hprefix tailTrace_7986878
  have hstable : (prefixWord ++ tailWord_7986878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986878).length < 2 ^ (prefixWord ++ tailWord_7986878).sum := by decide
  have hdescent : baseEnd_7986878 < baseStart_7986878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986897 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_7986897 : Nat := 118140960795 + 7986897 * 2 ^ 59
def prefixEnd_7986897 : Nat := 4983230072969 + 3 ^ 40 * 7986897 * 2
def baseEnd_7986897 : Nat := 4101117098952942962456435

theorem tailTrace_7986897 : CollatzResearch.WordTrace tailWord_7986897 prefixEnd_7986897 4101117098952942962456435 := by
  unfold tailWord_7986897
  simp only [CollatzResearch.WordTrace]
  refine ⟨291306065345843697254870945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194204043563895798169913963 291306065345843697254870945)
  ·
    refine ⟨218479549009382772941153209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291306065345843697254870945 218479549009382772941153209)
    ·
      refine ⟨163859661757037079705864907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218479549009382772941153209 163859661757037079705864907)
      ·
        refine ⟨245789492635555619558797361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163859661757037079705864907 245789492635555619558797361)
        ·
          refine ⟨184342119476666714669098021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245789492635555619558797361 184342119476666714669098021)
          ·
            refine ⟨34564147401875009000455879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184342119476666714669098021 34564147401875009000455879)
            ·
              refine ⟨51846221102812513500683819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34564147401875009000455879 51846221102812513500683819)
              ·
                refine ⟨77769331654218770251025729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51846221102812513500683819 77769331654218770251025729)
                ·
                  refine ⟨58326998740664077688269297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77769331654218770251025729 58326998740664077688269297)
                  ·
                    refine ⟨43745249055498058266201973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58326998740664077688269297 43745249055498058266201973)
                    ·
                      refine ⟨4101117098952942962456435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43745249055498058266201973 4101117098952942962456435)
                      ·
                        rfl

theorem cell23_7986897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_7986897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986897 prefixEnd_7986897 := by exact prefixLift 7986897
  have htrace : WordTrace (prefixWord ++ tailWord_7986897) baseStart_7986897 baseEnd_7986897 := by
    simpa [prefixWord, tailWord_7986897, baseEnd_7986897] using wordTrace_append hprefix tailTrace_7986897
  have hstable : (prefixWord ++ tailWord_7986897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986897).length < 2 ^ (prefixWord ++ tailWord_7986897).sum := by decide
  have hdescent : baseEnd_7986897 < baseStart_7986897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986911 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 1, 3, 2]
def baseStart_7986911 : Nat := 118140960795 + 7986911 * 2 ^ 59
def prefixEnd_7986911 : Nat := 4983230072969 + 3 ^ 40 * 7986911 * 2
def baseEnd_7986911 : Nat := 4101124287682105907681371

theorem tailTrace_7986911 : CollatzResearch.WordTrace tailWord_7986911 prefixEnd_7986911 4101124287682105907681371 := by
  unfold tailWord_7986911
  simp only [CollatzResearch.WordTrace]
  refine ⟨291306575967792977645880587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194204383978528651763920391 291306575967792977645880587)
  ·
    refine ⟨436959863951689466468820881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291306575967792977645880587 436959863951689466468820881)
    ·
      refine ⟨327719897963767099851615661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436959863951689466468820881 327719897963767099851615661)
      ·
        refine ⟨122894961736412662444355873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327719897963767099851615661 122894961736412662444355873)
        ·
          refine ⟨92171221302309496833266905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122894961736412662444355873 92171221302309496833266905)
          ·
            refine ⟨69128415976732122624950179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92171221302309496833266905 69128415976732122624950179)
            ·
              refine ⟨103692623965098183937425269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69128415976732122624950179 103692623965098183937425269)
              ·
                refine ⟨9721183496727954744133619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103692623965098183937425269 9721183496727954744133619)
                ·
                  refine ⟨14581775245091932116200429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721183496727954744133619 14581775245091932116200429)
                  ·
                    refine ⟨5468165716909474543575161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14581775245091932116200429 5468165716909474543575161)
                    ·
                      refine ⟨4101124287682105907681371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468165716909474543575161 4101124287682105907681371)
                      ·
                        rfl

theorem cell23_7986911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_7986911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986911 prefixEnd_7986911 := by exact prefixLift 7986911
  have htrace : WordTrace (prefixWord ++ tailWord_7986911) baseStart_7986911 baseEnd_7986911 := by
    simpa [prefixWord, tailWord_7986911, baseEnd_7986911] using wordTrace_append hprefix tailTrace_7986911
  have hstable : (prefixWord ++ tailWord_7986911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986911).length < 2 ^ (prefixWord ++ tailWord_7986911).sum := by decide
  have hdescent : baseEnd_7986911 < baseStart_7986911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986919 : List Nat := [1, 1, 5, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7986919 : Nat := 118140960795 + 7986919 * 2 ^ 59
def prefixEnd_7986919 : Nat := 4983230072969 + 3 ^ 40 * 7986919 * 2
def baseEnd_7986919 : Nat := 4101128395527341876381335

theorem tailTrace_7986919 : CollatzResearch.WordTrace tailWord_7986919 prefixEnd_7986919 4101128395527341876381335 := by
  unfold tailWord_7986919
  simp only [CollatzResearch.WordTrace]
  refine ⟨291306867751763995012171811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194204578501175996674781207 291306867751763995012171811)
  ·
    refine ⟨436960301627645992518257717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291306867751763995012171811 436960301627645992518257717)
    ·
      refine ⟨40965028277591811798586661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436960301627645992518257717 40965028277591811798586661)
      ·
        refine ⟨7680942802048464712234999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40965028277591811798586661 7680942802048464712234999)
        ·
          refine ⟨11521414203072697068352499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680942802048464712234999 11521414203072697068352499)
          ·
            refine ⟨17282121304609045602528749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11521414203072697068352499 17282121304609045602528749)
            ·
              refine ⟨6480795489228392100948281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282121304609045602528749 6480795489228392100948281)
              ·
                refine ⟨4860596616921294075711211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480795489228392100948281 4860596616921294075711211)
                ·
                  refine ⟨7290894925381941113566817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860596616921294075711211 7290894925381941113566817)
                  ·
                    refine ⟨5468171194036455835175113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290894925381941113566817 5468171194036455835175113)
                    ·
                      refine ⟨4101128395527341876381335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468171194036455835175113 4101128395527341876381335)
                      ·
                        rfl

theorem cell23_7986919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7986919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986919 prefixEnd_7986919 := by exact prefixLift 7986919
  have htrace : WordTrace (prefixWord ++ tailWord_7986919) baseStart_7986919 baseEnd_7986919 := by
    simpa [prefixWord, tailWord_7986919, baseEnd_7986919] using wordTrace_append hprefix tailTrace_7986919
  have hstable : (prefixWord ++ tailWord_7986919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986919).length < 2 ^ (prefixWord ++ tailWord_7986919).sum := by decide
  have hdescent : baseEnd_7986919 < baseStart_7986919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986927 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_7986927 : Nat := 118140960795 + 7986927 * 2 ^ 59
def prefixEnd_7986927 : Nat := 4983230072969 + 3 ^ 40 * 7986927 * 2
def baseEnd_7986927 : Nat := 4101132503372577845081297

theorem tailTrace_7986927 : CollatzResearch.WordTrace tailWord_7986927 prefixEnd_7986927 4101132503372577845081297 := by
  unfold tailWord_7986927
  simp only [CollatzResearch.WordTrace]
  refine ⟨291307159535735012378463035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194204773023823341585642023 291307159535735012378463035)
  ·
    refine ⟨436960739303602518567694553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291307159535735012378463035 436960739303602518567694553)
    ·
      refine ⟨327720554477701888925770915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436960739303602518567694553 327720554477701888925770915)
      ·
        refine ⟨491580831716552833388656373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327720554477701888925770915 491580831716552833388656373)
        ·
          refine ⟨46085702973426828130186535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491580831716552833388656373 46085702973426828130186535)
          ·
            refine ⟨69128554460140242195279803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46085702973426828130186535 69128554460140242195279803)
            ·
              refine ⟨103692831690210363292919705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69128554460140242195279803 103692831690210363292919705)
              ·
                refine ⟨77769623767657772469689779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103692831690210363292919705 77769623767657772469689779)
                ·
                  refine ⟨116654435651486658704534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77769623767657772469689779 116654435651486658704534669)
                  ·
                    refine ⟨43745413369307497014200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116654435651486658704534669 43745413369307497014200501)
                    ·
                      refine ⟨4101132503372577845081297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43745413369307497014200501 4101132503372577845081297)
                      ·
                        rfl

theorem cell23_7986927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_7986927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986927 prefixEnd_7986927 := by exact prefixLift 7986927
  have htrace : WordTrace (prefixWord ++ tailWord_7986927) baseStart_7986927 baseEnd_7986927 := by
    simpa [prefixWord, tailWord_7986927, baseEnd_7986927] using wordTrace_append hprefix tailTrace_7986927
  have hstable : (prefixWord ++ tailWord_7986927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986927).length < 2 ^ (prefixWord ++ tailWord_7986927).sum := by decide
  have hdescent : baseEnd_7986927 < baseStart_7986927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986941 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_7986941 : Nat := 118140960795 + 7986941 * 2 ^ 59
def prefixEnd_7986941 : Nat := 4983230072969 + 3 ^ 40 * 7986941 * 2
def baseEnd_7986941 : Nat := 4101139692101740790306233

theorem tailTrace_7986941 : CollatzResearch.WordTrace tailWord_7986941 prefixEnd_7986941 4101139692101740790306233 := by
  unfold tailWord_7986941
  simp only [CollatzResearch.WordTrace]
  refine ⟨291307670157684292769472677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194205113438456195179648451 291307670157684292769472677)
  ·
    refine ⟨54620188154565804894276127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291307670157684292769472677 54620188154565804894276127)
    ·
      refine ⟨81930282231848707341414191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54620188154565804894276127 81930282231848707341414191)
      ·
        refine ⟨122895423347773061012121287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81930282231848707341414191 122895423347773061012121287)
        ·
          refine ⟨184343135021659591518181931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122895423347773061012121287 184343135021659591518181931)
          ·
            refine ⟨276514702532489387277272897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184343135021659591518181931 276514702532489387277272897)
            ·
              refine ⟨207386026899367040457954673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276514702532489387277272897 207386026899367040457954673)
              ·
                refine ⟨155539520174525280343466005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207386026899367040457954673 155539520174525280343466005)
                ·
                  refine ⟨7290915008180872516099969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155539520174525280343466005 7290915008180872516099969)
                  ·
                    refine ⟨5468186256135654387074977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7290915008180872516099969 5468186256135654387074977)
                    ·
                      refine ⟨4101139692101740790306233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468186256135654387074977 4101139692101740790306233)
                      ·
                        rfl

theorem cell23_7986941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_7986941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986941 prefixEnd_7986941 := by exact prefixLift 7986941
  have htrace : WordTrace (prefixWord ++ tailWord_7986941) baseStart_7986941 baseEnd_7986941 := by
    simpa [prefixWord, tailWord_7986941, baseEnd_7986941] using wordTrace_append hprefix tailTrace_7986941
  have hstable : (prefixWord ++ tailWord_7986941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986941).length < 2 ^ (prefixWord ++ tailWord_7986941).sum := by decide
  have hdescent : baseEnd_7986941 < baseStart_7986941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986947 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 7]
def baseStart_7986947 : Nat := 118140960795 + 7986947 * 2 ^ 59
def prefixEnd_7986947 : Nat := 4983230072969 + 3 ^ 40 * 7986947 * 2
def baseEnd_7986947 : Nat := 455682530331740862981245

theorem tailTrace_7986947 : CollatzResearch.WordTrace tailWord_7986947 prefixEnd_7986947 455682530331740862981245 := by
  unfold tailWord_7986947
  simp only [CollatzResearch.WordTrace]
  refine ⟨291307888995662555794191095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194205259330441703862794063 291307888995662555794191095)
  ·
    refine ⟨436961833493493833691286643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291307888995662555794191095 436961833493493833691286643)
    ·
      refine ⟨655442750240240750536929965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436961833493493833691286643 655442750240240750536929965)
      ·
        refine ⟨245791031340090281451348737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655442750240240750536929965 245791031340090281451348737)
        ·
          refine ⟨184343273505067711088511553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245791031340090281451348737 184343273505067711088511553)
          ·
            refine ⟨138257455128800783316383665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184343273505067711088511553 138257455128800783316383665)
            ·
              refine ⟨103693091346600587487287749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138257455128800783316383665 103693091346600587487287749)
              ·
                refine ⟨19442454627487610153866453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103693091346600587487287749 19442454627487610153866453)
                ·
                  refine ⟨455682530331740862981245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19442454627487610153866453 455682530331740862981245)
                  ·
                    rfl

theorem cell23_7986947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 7].length) (baseStart_7986947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986947 prefixEnd_7986947 := by exact prefixLift 7986947
  have htrace : WordTrace (prefixWord ++ tailWord_7986947) baseStart_7986947 baseEnd_7986947 := by
    simpa [prefixWord, tailWord_7986947, baseEnd_7986947] using wordTrace_append hprefix tailTrace_7986947
  have hstable : (prefixWord ++ tailWord_7986947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986947).length < 2 ^ (prefixWord ++ tailWord_7986947).sum := by decide
  have hdescent : baseEnd_7986947 < baseStart_7986947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986962 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7986962 : Nat := 118140960795 + 7986962 * 2 ^ 59
def prefixEnd_7986962 : Nat := 4983230072969 + 3 ^ 40 * 7986962 * 2
def baseEnd_7986962 : Nat := 4101150475195485208143637

theorem tailTrace_7986962 : CollatzResearch.WordTrace tailWord_7986962 prefixEnd_7986962 4101150475195485208143637 := by
  unfold tailWord_7986962
  simp only [CollatzResearch.WordTrace]
  refine ⟨72827109022652053338996785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194205624060405475570658093 72827109022652053338996785)
  ·
    refine ⟨54620331766989040004247589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72827109022652053338996785 54620331766989040004247589)
    ·
      refine ⟨10241312206310445000796423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54620331766989040004247589 10241312206310445000796423)
      ·
        refine ⟨15361968309465667501194635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241312206310445000796423 15361968309465667501194635)
        ·
          refine ⟨23042952464198501251791953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15361968309465667501194635 23042952464198501251791953)
          ·
            refine ⟨17282214348148875938843965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23042952464198501251791953 17282214348148875938843965)
            ·
              refine ⟨6480830380555828477066487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282214348148875938843965 6480830380555828477066487)
              ·
                refine ⟨9721245570833742715599731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480830380555828477066487 9721245570833742715599731)
                ·
                  refine ⟨14581868356250614073399597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721245570833742715599731 14581868356250614073399597)
                  ·
                    refine ⟨5468200633593980277524849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14581868356250614073399597 5468200633593980277524849)
                    ·
                      refine ⟨4101150475195485208143637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468200633593980277524849 4101150475195485208143637)
                      ·
                        rfl

theorem cell23_7986962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7986962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986962 prefixEnd_7986962 := by exact prefixLift 7986962
  have htrace : WordTrace (prefixWord ++ tailWord_7986962) baseStart_7986962 baseEnd_7986962 := by
    simpa [prefixWord, tailWord_7986962, baseEnd_7986962] using wordTrace_append hprefix tailTrace_7986962
  have hstable : (prefixWord ++ tailWord_7986962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986962).length < 2 ^ (prefixWord ++ tailWord_7986962).sum := by decide
  have hdescent : baseEnd_7986962 < baseStart_7986962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986981 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 5]
def baseStart_7986981 : Nat := 118140960795 + 7986981 * 2 ^ 59
def prefixEnd_7986981 : Nat := 4983230072969 + 3 ^ 40 * 7986981 * 2
def baseEnd_7986981 : Nat := 455684470147546737089561

theorem tailTrace_7986981 : CollatzResearch.WordTrace tailWord_7986981 prefixEnd_7986981 455684470147546737089561 := by
  unfold tailWord_7986981
  simp only [CollatzResearch.WordTrace]
  refine ⟨291309129077539379600928797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194206086051692919733952531 291309129077539379600928797)
  ·
    refine ⟨109240923404077267350348299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291309129077539379600928797 109240923404077267350348299)
    ·
      refine ⟨163861385106115901025522449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109240923404077267350348299 163861385106115901025522449)
      ·
        refine ⟨122896038829586925769141837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163861385106115901025522449 122896038829586925769141837)
        ·
          refine ⟨46086014561095097163428189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122896038829586925769141837 46086014561095097163428189)
          ·
            refine ⟨17282255460410661436285571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46086014561095097163428189 17282255460410661436285571)
            ·
              refine ⟨25923383190615992154428357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17282255460410661436285571 25923383190615992154428357)
              ·
                refine ⟨4860634348240498528955317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25923383190615992154428357 4860634348240498528955317)
                ·
                  refine ⟨455684470147546737089561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860634348240498528955317 455684470147546737089561)
                  ·
                    rfl

theorem cell23_7986981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_7986981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986981 prefixEnd_7986981 := by exact prefixLift 7986981
  have htrace : WordTrace (prefixWord ++ tailWord_7986981) baseStart_7986981 baseEnd_7986981 := by
    simpa [prefixWord, tailWord_7986981, baseEnd_7986981] using wordTrace_append hprefix tailTrace_7986981
  have hstable : (prefixWord ++ tailWord_7986981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986981).length < 2 ^ (prefixWord ++ tailWord_7986981).sum := by decide
  have hdescent : baseEnd_7986981 < baseStart_7986981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7986987 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_7986987 : Nat := 118140960795 + 7986987 * 2 ^ 59
def prefixEnd_7986987 : Nat := 4983230072969 + 3 ^ 40 * 7986987 * 2
def baseEnd_7986987 : Nat := 4101163312211847610331021

theorem tailTrace_7986987 : CollatzResearch.WordTrace tailWord_7986987 prefixEnd_7986987 4101163312211847610331021 := by
  unfold tailWord_7986987
  simp only [CollatzResearch.WordTrace]
  refine ⟨291309347915517642625647215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194206231943678428417098143 291309347915517642625647215)
  ·
    refine ⟨436964021873276463938470823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291309347915517642625647215 436964021873276463938470823)
    ·
      refine ⟨655446032809914695907706235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436964021873276463938470823 655446032809914695907706235)
      ·
        refine ⟨983169049214872043861559353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655446032809914695907706235 983169049214872043861559353)
        ·
          refine ⟨737376786911154032896169515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983169049214872043861559353 737376786911154032896169515)
          ·
            refine ⟨1106065180366731049344254273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737376786911154032896169515 1106065180366731049344254273)
            ·
              refine ⟨829548885275048287008190705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106065180366731049344254273 829548885275048287008190705)
              ·
                refine ⟨622161663956286215256143029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829548885275048287008190705 622161663956286215256143029)
                ·
                  refine ⟨58327655995901832680263409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622161663956286215256143029 58327655995901832680263409)
                  ·
                    refine ⟨43745741996926374510197557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58327655995901832680263409 43745741996926374510197557)
                    ·
                      refine ⟨4101163312211847610331021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43745741996926374510197557 4101163312211847610331021)
                      ·
                        rfl

theorem cell23_7986987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_7986987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7986987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7986987 prefixEnd_7986987 := by exact prefixLift 7986987
  have htrace : WordTrace (prefixWord ++ tailWord_7986987) baseStart_7986987 baseEnd_7986987 := by
    simpa [prefixWord, tailWord_7986987, baseEnd_7986987] using wordTrace_append hprefix tailTrace_7986987
  have hstable : (prefixWord ++ tailWord_7986987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7986987).length < 2 ^ (prefixWord ++ tailWord_7986987).sum := by decide
  have hdescent : baseEnd_7986987 < baseStart_7986987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7986987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987011 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 2, 5]
def baseStart_7987011 : Nat := 118140960795 + 7987011 * 2 ^ 59
def prefixEnd_7987011 : Nat := 4983230072969 + 3 ^ 40 * 7987011 * 2
def baseEnd_7987011 : Nat := 1367058545249185172143637

theorem tailTrace_7987011 : CollatzResearch.WordTrace tailWord_7987011 prefixEnd_7987011 1367058545249185172143637 := by
  unfold tailWord_7987011
  simp only [CollatzResearch.WordTrace]
  refine ⟨291310223267430694724520887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194206815511620463149680591 291310223267430694724520887)
  ·
    refine ⟨436965334901146042086781331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291310223267430694724520887 436965334901146042086781331)
    ·
      refine ⟨655448002351719063130171997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436965334901146042086781331 655448002351719063130171997)
      ·
        refine ⟨245793000881894648673814499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655448002351719063130171997 245793000881894648673814499)
        ·
          refine ⟨368689501322841973010721749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245793000881894648673814499 368689501322841973010721749)
          ·
            refine ⟨8641160187254108742438791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368689501322841973010721749 8641160187254108742438791)
            ·
              refine ⟨12961740280881163113658187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641160187254108742438791 12961740280881163113658187)
              ·
                refine ⟨19442610421321744670487281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961740280881163113658187 19442610421321744670487281)
                ·
                  refine ⟨14581957815991308502865461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19442610421321744670487281 14581957815991308502865461)
                  ·
                    refine ⟨1367058545249185172143637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14581957815991308502865461 1367058545249185172143637)
                    ·
                      rfl

theorem cell23_7987011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 5].length) (baseStart_7987011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987011 prefixEnd_7987011 := by exact prefixLift 7987011
  have htrace : WordTrace (prefixWord ++ tailWord_7987011) baseStart_7987011 baseEnd_7987011 := by
    simpa [prefixWord, tailWord_7987011, baseEnd_7987011] using wordTrace_append hprefix tailTrace_7987011
  have hstable : (prefixWord ++ tailWord_7987011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987011).length < 2 ^ (prefixWord ++ tailWord_7987011).sum := by decide
  have hdescent : baseEnd_7987011 < baseStart_7987011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987024 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_7987024 : Nat := 118140960795 + 7987024 * 2 ^ 59
def prefixEnd_7987024 : Nat := 4983230072969 + 3 ^ 40 * 7987024 * 2
def baseEnd_7987024 : Nat := 1367060770332021321856117

theorem tailTrace_7987024 : CollatzResearch.WordTrace tailWord_7987024 prefixEnd_7987024 1367060770332021321856117 := by
  unfold tailWord_7987024
  simp only [CollatzResearch.WordTrace]
  refine ⟨145655348708191798972372063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194207131610922398629829417 145655348708191798972372063)
  ·
    refine ⟨218483023062287698458558095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145655348708191798972372063 218483023062287698458558095)
    ·
      refine ⟨327724534593431547687837143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218483023062287698458558095 327724534593431547687837143)
      ·
        refine ⟨491586801890147321531755715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327724534593431547687837143 491586801890147321531755715)
        ·
          refine ⟨737380202835220982297633573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491586801890147321531755715 737380202835220982297633573)
          ·
            refine ⟨138258788031603934180806295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 737380202835220982297633573 138258788031603934180806295)
            ·
              refine ⟨207388182047405901271209443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138258788031603934180806295 207388182047405901271209443)
              ·
                refine ⟨311082273071108851906814165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207388182047405901271209443 311082273071108851906814165)
                ·
                  refine ⟨7290990775104113716565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 311082273071108851906814165 7290990775104113716565957)
                  ·
                    refine ⟨1367060770332021321856117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7290990775104113716565957 1367060770332021321856117)
                    ·
                      rfl

theorem cell23_7987024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_7987024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987024 prefixEnd_7987024 := by exact prefixLift 7987024
  have htrace : WordTrace (prefixWord ++ tailWord_7987024) baseStart_7987024 baseEnd_7987024 := by
    simpa [prefixWord, tailWord_7987024, baseEnd_7987024] using wordTrace_append hprefix tailTrace_7987024
  have hstable : (prefixWord ++ tailWord_7987024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987024).length < 2 ^ (prefixWord ++ tailWord_7987024).sum := by decide
  have hdescent : baseEnd_7987024 < baseStart_7987024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987041 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7987041 : Nat := 118140960795 + 7987041 * 2 ^ 59
def prefixEnd_7987041 : Nat := 4983230072969 + 3 ^ 40 * 7987041 * 2
def baseEnd_7987041 : Nat := 1367063680055730133018591

theorem tailTrace_7987041 : CollatzResearch.WordTrace tailWord_7987041 prefixEnd_7987041 1367063680055730133018591 := by
  unfold tailWord_7987041
  simp only [CollatzResearch.WordTrace]
  refine ⟨291311317457322009848112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194207544971548006565408651 291311317457322009848112977)
  ·
    refine ⟨218483488092991507386084733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291311317457322009848112977 218483488092991507386084733)
    ·
      refine ⟨81931308034871815269781775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218483488092991507386084733 81931308034871815269781775)
      ·
        refine ⟨122896962052307722904672663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81931308034871815269781775 122896962052307722904672663)
        ·
          refine ⟨184345443078461584357008995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122896962052307722904672663 184345443078461584357008995)
          ·
            refine ⟨276518164617692376535513493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184345443078461584357008995 276518164617692376535513493)
            ·
              refine ⟨12961788966454330150102195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276518164617692376535513493 12961788966454330150102195)
              ·
                refine ⟨19442683449681495225153293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961788966454330150102195 19442683449681495225153293)
                ·
                  refine ⟨7291006293630560709432485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19442683449681495225153293 7291006293630560709432485)
                  ·
                    refine ⟨1367063680055730133018591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291006293630560709432485 1367063680055730133018591)
                    ·
                      rfl

theorem cell23_7987041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7987041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987041 prefixEnd_7987041 := by exact prefixLift 7987041
  have htrace : WordTrace (prefixWord ++ tailWord_7987041) baseStart_7987041 baseEnd_7987041 := by
    simpa [prefixWord, tailWord_7987041, baseEnd_7987041] using wordTrace_append hprefix tailTrace_7987041
  have hstable : (prefixWord ++ tailWord_7987041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987041).length < 2 ^ (prefixWord ++ tailWord_7987041).sum := by decide
  have hdescent : baseEnd_7987041 < baseStart_7987041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987075 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 1, 4]
def baseStart_7987075 : Nat := 118140960795 + 7987075 * 2 ^ 59
def prefixEnd_7987075 : Nat := 4983230072969 + 3 ^ 40 * 7987075 * 2
def baseEnd_7987075 : Nat := 1367069499503147755343539

theorem tailTrace_7987075 : CollatzResearch.WordTrace tailWord_7987075 prefixEnd_7987075 1367069499503147755343539 := by
  unfold tailWord_7987075
  simp only [CollatzResearch.WordTrace]
  refine ⟨291312557539198833654850679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194208371692799222436567119 291312557539198833654850679)
  ·
    refine ⟨436968836308798250482276019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291312557539198833654850679 436968836308798250482276019)
    ·
      refine ⟨655453254463197375723414029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436968836308798250482276019 655453254463197375723414029)
      ·
        refine ⟨245794970423699015896280261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655453254463197375723414029 245794970423699015896280261)
        ·
          refine ⟨46086556954443565480552549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245794970423699015896280261 46086556954443565480552549)
          ·
            refine ⟨8641229428958168527603603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46086556954443565480552549 8641229428958168527603603)
            ·
              refine ⟨12961844143437252791405405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641229428958168527603603 12961844143437252791405405)
              ·
                refine ⟨4860691553788969796777027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12961844143437252791405405 4860691553788969796777027)
                ·
                  refine ⟨7291037330683454695165541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860691553788969796777027 7291037330683454695165541)
                  ·
                    refine ⟨1367069499503147755343539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291037330683454695165541 1367069499503147755343539)
                    ·
                      rfl

theorem cell23_7987075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 4].length) (baseStart_7987075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987075 prefixEnd_7987075 := by exact prefixLift 7987075
  have htrace : WordTrace (prefixWord ++ tailWord_7987075) baseStart_7987075 baseEnd_7987075 := by
    simpa [prefixWord, tailWord_7987075, baseEnd_7987075] using wordTrace_append hprefix tailTrace_7987075
  have hstable : (prefixWord ++ tailWord_7987075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987075).length < 2 ^ (prefixWord ++ tailWord_7987075).sum := by decide
  have hdescent : baseEnd_7987075 < baseStart_7987075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987084 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_7987084 : Nat := 118140960795 + 7987084 * 2 ^ 59
def prefixEnd_7987084 : Nat := 4983230072969 + 3 ^ 40 * 7987084 * 2
def baseEnd_7987084 : Nat := 1367071039945111243606025

theorem tailTrace_7987084 : CollatzResearch.WordTrace tailWord_7987084 prefixEnd_7987084 1367071039945111243606025 := by
  unfold tailWord_7987084
  simp only [CollatzResearch.WordTrace]
  refine ⟨145656442898083114095964153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194208590530777485461285537 145656442898083114095964153)
  ·
    refine ⟨109242332173562335571973115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145656442898083114095964153 109242332173562335571973115)
    ·
      refine ⟨163863498260343503357959673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109242332173562335571973115 163863498260343503357959673)
      ·
        refine ⟨122897623695257627518469755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163863498260343503357959673 122897623695257627518469755)
        ·
          refine ⟨184346435542886441277704633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122897623695257627518469755 184346435542886441277704633)
          ·
            refine ⟨138259826657164830958278475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184346435542886441277704633 138259826657164830958278475)
            ·
              refine ⟨207389739985747246437417713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138259826657164830958278475 207389739985747246437417713)
              ·
                refine ⟨155542304989310434828063285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207389739985747246437417713 155542304989310434828063285)
                ·
                  refine ⟨14582091092747853265130933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155542304989310434828063285 14582091092747853265130933)
                  ·
                    refine ⟨1367071039945111243606025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14582091092747853265130933 1367071039945111243606025)
                    ·
                      rfl

theorem cell23_7987084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_7987084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987084 prefixEnd_7987084 := by exact prefixLift 7987084
  have htrace : WordTrace (prefixWord ++ tailWord_7987084) baseStart_7987084 baseEnd_7987084 := by
    simpa [prefixWord, tailWord_7987084, baseEnd_7987084] using wordTrace_append hprefix tailTrace_7987084
  have hstable : (prefixWord ++ tailWord_7987084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987084).length < 2 ^ (prefixWord ++ tailWord_7987084).sum := by decide
  have hdescent : baseEnd_7987084 < baseStart_7987084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987092 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7987092 : Nat := 118140960795 + 7987092 * 2 ^ 59
def prefixEnd_7987092 : Nat := 4983230072969 + 3 ^ 40 * 7987092 * 2
def baseEnd_7987092 : Nat := 1367072409226856566506013

theorem tailTrace_7987092 : CollatzResearch.WordTrace tailWord_7987092 prefixEnd_7987092 1367072409226856566506013 := by
  unfold tailWord_7987092
  simp only [CollatzResearch.WordTrace]
  refine ⟨145656588790068622779109765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194208785053424830372146353 145656588790068622779109765)
  ·
    refine ⟨27310610398137866771083081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145656588790068622779109765 27310610398137866771083081)
    ·
      refine ⟨20482957798603400078312311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27310610398137866771083081 20482957798603400078312311)
      ·
        refine ⟨30724436697905100117468467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20482957798603400078312311 30724436697905100117468467)
        ·
          refine ⟨46086655046857650176202701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30724436697905100117468467 46086655046857650176202701)
          ·
            refine ⟨17282495642571618816076013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46086655046857650176202701 17282495642571618816076013)
            ·
              refine ⟨6480935865964357056028505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282495642571618816076013 6480935865964357056028505)
              ·
                refine ⟨4860701899473267792021379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480935865964357056028505 4860701899473267792021379)
                ·
                  refine ⟨7291052849209901688032069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860701899473267792021379 7291052849209901688032069)
                  ·
                    refine ⟨1367072409226856566506013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291052849209901688032069 1367072409226856566506013)
                    ·
                      rfl

theorem cell23_7987092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7987092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987092 prefixEnd_7987092 := by exact prefixLift 7987092
  have htrace : WordTrace (prefixWord ++ tailWord_7987092) baseStart_7987092 baseEnd_7987092 := by
    simpa [prefixWord, tailWord_7987092, baseEnd_7987092] using wordTrace_append hprefix tailTrace_7987092
  have hstable : (prefixWord ++ tailWord_7987092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987092).length < 2 ^ (prefixWord ++ tailWord_7987092).sum := by decide
  have hdescent : baseEnd_7987092 < baseStart_7987092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987104 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_7987104 : Nat := 118140960795 + 7987104 * 2 ^ 59
def prefixEnd_7987104 : Nat := 4983230072969 + 3 ^ 40 * 7987104 * 2
def baseEnd_7987104 : Nat := 4101223389448423652567983

theorem tailTrace_7987104 : CollatzResearch.WordTrace tailWord_7987104 prefixEnd_7987104 4101223389448423652567983 := by
  unfold tailWord_7987104
  simp only [CollatzResearch.WordTrace]
  refine ⟨145656807628046885803828183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194209076837395847738437577 145656807628046885803828183)
  ·
    refine ⟨218485211442070328705742275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145656807628046885803828183 218485211442070328705742275)
    ·
      refine ⟨327727817163105493058613413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218485211442070328705742275 327727817163105493058613413)
      ·
        refine ⟨61448965718082279948490015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327727817163105493058613413 61448965718082279948490015)
        ·
          refine ⟨92173448577123419922735023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61448965718082279948490015 92173448577123419922735023)
          ·
            refine ⟨138260172865685129884102535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92173448577123419922735023 138260172865685129884102535)
            ·
              refine ⟨207390259298527694826153803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138260172865685129884102535 207390259298527694826153803)
              ·
                refine ⟨311085388947791542239230705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207390259298527694826153803 311085388947791542239230705)
                ·
                  refine ⟨233314041710843656679423029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311085388947791542239230705 233314041710843656679423029)
                  ·
                    refine ⟨21873191410391592813695909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233314041710843656679423029 21873191410391592813695909)
                    ·
                      refine ⟨4101223389448423652567983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21873191410391592813695909 4101223389448423652567983)
                      ·
                        rfl

theorem cell23_7987104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_7987104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987104 prefixEnd_7987104 := by exact prefixLift 7987104
  have htrace : WordTrace (prefixWord ++ tailWord_7987104) baseStart_7987104 baseEnd_7987104 := by
    simpa [prefixWord, tailWord_7987104, baseEnd_7987104] using wordTrace_append hprefix tailTrace_7987104
  have hstable : (prefixWord ++ tailWord_7987104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987104).length < 2 ^ (prefixWord ++ tailWord_7987104).sum := by decide
  have hdescent : baseEnd_7987104 < baseStart_7987104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987105 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 6]
def baseStart_7987105 : Nat := 118140960795 + 7987105 * 2 ^ 59
def prefixEnd_7987105 : Nat := 4983230072969 + 3 ^ 40 * 7987105 * 2
def baseEnd_7987105 : Nat := 455691544769897572072831

theorem tailTrace_7987105 : CollatzResearch.WordTrace tailWord_7987105 prefixEnd_7987105 455691544769897572072831 := by
  unfold tailWord_7987105
  simp only [CollatzResearch.WordTrace]
  refine ⟨291313651729090148778442769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194209101152726765852295179 291313651729090148778442769)
  ·
    refine ⟨218485238796817611583832077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291313651729090148778442769 218485238796817611583832077)
    ·
      refine ⟨81931964548806604343937029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218485238796817611583832077 81931964548806604343937029)
      ·
        refine ⟨15362243352901238314488193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81931964548806604343937029 15362243352901238314488193)
        ·
          refine ⟨11521682514675928735866145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15362243352901238314488193 11521682514675928735866145)
          ·
            refine ⟨8641261886006946551899609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11521682514675928735866145 8641261886006946551899609)
            ·
              refine ⟨6480946414505209913924707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8641261886006946551899609 6480946414505209913924707)
              ·
                refine ⟨9721419621757814870887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480946414505209913924707 9721419621757814870887061)
                ·
                  refine ⟨455691544769897572072831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9721419621757814870887061 455691544769897572072831)
                  ·
                    rfl

theorem cell23_7987105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_7987105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987105 prefixEnd_7987105 := by exact prefixLift 7987105
  have htrace : WordTrace (prefixWord ++ tailWord_7987105) baseStart_7987105 baseEnd_7987105 := by
    simpa [prefixWord, tailWord_7987105, baseEnd_7987105] using wordTrace_append hprefix tailTrace_7987105
  have hstable : (prefixWord ++ tailWord_7987105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987105).length < 2 ^ (prefixWord ++ tailWord_7987105).sum := by decide
  have hdescent : baseEnd_7987105 < baseStart_7987105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987125 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7987125 : Nat := 118140960795 + 7987125 * 2 ^ 59
def prefixEnd_7987125 : Nat := 4983230072969 + 3 ^ 40 * 7987125 * 2
def baseEnd_7987125 : Nat := 4101234172542168070405387

theorem tailTrace_7987125 : CollatzResearch.WordTrace tailWord_7987125 prefixEnd_7987125 4101234172542168070405387 := by
  unfold tailWord_7987125
  simp only [CollatzResearch.WordTrace]
  refine ⟨291314381189017692194170829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194209587459345128129447219 291314381189017692194170829)
  ·
    refine ⟨109242892945881634572814061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291314381189017692194170829 109242892945881634572814061)
    ·
      refine ⟨40966084854705612964805273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109242892945881634572814061 40966084854705612964805273)
      ·
        refine ⟨30724563641029209723603955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40966084854705612964805273 30724563641029209723603955)
        ·
          refine ⟨46086845461543814585405933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30724563641029209723603955 46086845461543814585405933)
          ·
            refine ⟨17282567048078930469527225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46086845461543814585405933 17282567048078930469527225)
            ·
              refine ⟨12961925286059197852145419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17282567048078930469527225 12961925286059197852145419)
              ·
                refine ⟨19442887929088796778218129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961925286059197852145419 19442887929088796778218129)
                ·
                  refine ⟨14582165946816597583663597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19442887929088796778218129 14582165946816597583663597)
                  ·
                    refine ⟨5468312230056224093873849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14582165946816597583663597 5468312230056224093873849)
                    ·
                      refine ⟨4101234172542168070405387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468312230056224093873849 4101234172542168070405387)
                      ·
                        rfl

theorem cell23_7987125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7987125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987125 prefixEnd_7987125 := by exact prefixLift 7987125
  have htrace : WordTrace (prefixWord ++ tailWord_7987125) baseStart_7987125 baseEnd_7987125 := by
    simpa [prefixWord, tailWord_7987125, baseEnd_7987125] using wordTrace_append hprefix tailTrace_7987125
  have hstable : (prefixWord ++ tailWord_7987125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987125).length < 2 ^ (prefixWord ++ tailWord_7987125).sum := by decide
  have hdescent : baseEnd_7987125 < baseStart_7987125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987144 : List Nat := [2, 1, 3, 1, 4, 12]
def baseStart_7987144 : Nat := 118140960795 + 7987144 * 2 ^ 59
def prefixEnd_7987144 : Nat := 4983230072969 + 3 ^ 40 * 7987144 * 2
def baseEnd_7987144 : Nat := 16877547031582730436493

theorem tailTrace_7987144 : CollatzResearch.WordTrace tailWord_7987144 prefixEnd_7987144 16877547031582730436493 := by
  unfold tailWord_7987144
  simp only [CollatzResearch.WordTrace]
  refine ⟨145657537087974429219556243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194210049450632572292741657 145657537087974429219556243)
  ·
    refine ⟨218486305631961643829334365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145657537087974429219556243 218486305631961643829334365)
    ·
      refine ⟨81932364611985616436000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218486305631961643829334365 81932364611985616436000387)
      ·
        refine ⟨122898546917978424654000581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81932364611985616436000387 122898546917978424654000581)
        ·
          refine ⟨23043477547120954622625109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122898546917978424654000581 23043477547120954622625109)
          ·
            refine ⟨16877547031582730436493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23043477547120954622625109 16877547031582730436493)
            ·
              rfl

theorem cell23_7987144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 12].length) (baseStart_7987144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987144 prefixEnd_7987144 := by exact prefixLift 7987144
  have htrace : WordTrace (prefixWord ++ tailWord_7987144) baseStart_7987144 baseEnd_7987144 := by
    simpa [prefixWord, tailWord_7987144, baseEnd_7987144] using wordTrace_append hprefix tailTrace_7987144
  have hstable : (prefixWord ++ tailWord_7987144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987144).length < 2 ^ (prefixWord ++ tailWord_7987144).sum := by decide
  have hdescent : baseEnd_7987144 < baseStart_7987144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987148 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_7987148 : Nat := 118140960795 + 7987148 * 2 ^ 59
def prefixEnd_7987148 : Nat := 4983230072969 + 3 ^ 40 * 7987148 * 2
def baseEnd_7987148 : Nat := 1367081994199073826805927

theorem tailTrace_7987148 : CollatzResearch.WordTrace tailWord_7987148 prefixEnd_7987148 1367081994199073826805927 := by
  unfold tailWord_7987148
  simp only [CollatzResearch.WordTrace]
  refine ⟨145657610033967183561129049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194210146711956244748172065 145657610033967183561129049)
  ·
    refine ⟨109243207525475387670846787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145657610033967183561129049 109243207525475387670846787)
    ·
      refine ⟨163864811288213081506270181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109243207525475387670846787 163864811288213081506270181)
      ·
        refine ⟨30724652116539952782425659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163864811288213081506270181 30724652116539952782425659)
        ·
          refine ⟨46086978174809929173638489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30724652116539952782425659 46086978174809929173638489)
          ·
            refine ⟨34565233631107446880228867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46086978174809929173638489 34565233631107446880228867)
            ·
              refine ⟨51847850446661170320343301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34565233631107446880228867 51847850446661170320343301)
              ·
                refine ⟨9721471958748969435064369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51847850446661170320343301 9721471958748969435064369)
                ·
                  refine ⟨7291103969061727076298277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721471958748969435064369 7291103969061727076298277)
                  ·
                    refine ⟨1367081994199073826805927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291103969061727076298277 1367081994199073826805927)
                    ·
                      rfl

theorem cell23_7987148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_7987148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987148 prefixEnd_7987148 := by exact prefixLift 7987148
  have htrace : WordTrace (prefixWord ++ tailWord_7987148) baseStart_7987148 baseEnd_7987148 := by
    simpa [prefixWord, tailWord_7987148, baseEnd_7987148] using wordTrace_append hprefix tailTrace_7987148
  have hstable : (prefixWord ++ tailWord_7987148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987148).length < 2 ^ (prefixWord ++ tailWord_7987148).sum := by decide
  have hdescent : baseEnd_7987148 < baseStart_7987148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987205 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_7987205 : Nat := 118140960795 + 7987205 * 2 ^ 59
def prefixEnd_7987205 : Nat := 4983230072969 + 3 ^ 40 * 7987205 * 2
def baseEnd_7987205 : Nat := 4101275250994527757405019

theorem tailTrace_7987205 : CollatzResearch.WordTrace tailWord_7987205 prefixEnd_7987205 4101275250994527757405019 := by
  unfold tailWord_7987205
  simp only [CollatzResearch.WordTrace]
  refine ⟨291317299028727865857083069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194211532685818577238055379 291317299028727865857083069)
  ·
    refine ⟨109243987135772949696406151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291317299028727865857083069 109243987135772949696406151)
    ·
      refine ⟨163865980703659424544609227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109243987135772949696406151 163865980703659424544609227)
      ·
        refine ⟨245798971055489136816913841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163865980703659424544609227 245798971055489136816913841)
        ·
          refine ⟨184349228291616852612685381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245798971055489136816913841 184349228291616852612685381)
          ·
            refine ⟨34565480304678159864878509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184349228291616852612685381 34565480304678159864878509)
            ·
              refine ⟨12962055114254309949329441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34565480304678159864878509 12962055114254309949329441)
              ·
                refine ⟨9721541335690732461997081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962055114254309949329441 9721541335690732461997081)
                ·
                  refine ⟨7291156001768049346497811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721541335690732461997081 7291156001768049346497811)
                  ·
                    refine ⟨10936734002652074019746717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291156001768049346497811 10936734002652074019746717)
                    ·
                      refine ⟨4101275250994527757405019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10936734002652074019746717 4101275250994527757405019)
                      ·
                        rfl

theorem cell23_7987205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_7987205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987205 prefixEnd_7987205 := by exact prefixLift 7987205
  have htrace : WordTrace (prefixWord ++ tailWord_7987205) baseStart_7987205 baseEnd_7987205 := by
    simpa [prefixWord, tailWord_7987205, baseEnd_7987205] using wordTrace_append hprefix tailTrace_7987205
  have hstable : (prefixWord ++ tailWord_7987205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987205).length < 2 ^ (prefixWord ++ tailWord_7987205).sum := by decide
  have hdescent : baseEnd_7987205 < baseStart_7987205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987231 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7987231 : Nat := 118140960795 + 7987231 * 2 ^ 59
def prefixEnd_7987231 : Nat := 4983230072969 + 3 ^ 40 * 7987231 * 2
def baseEnd_7987231 : Nat := 4101288601491544655679899

theorem tailTrace_7987231 : CollatzResearch.WordTrace tailWord_7987231 prefixEnd_7987231 4101288601491544655679899 := by
  unfold tailWord_7987231
  simp only [CollatzResearch.WordTrace]
  refine ⟨291318247326633672297529547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194212164884422448198353031 291318247326633672297529547)
  ·
    refine ⟨436977370989950508446294321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291318247326633672297529547 436977370989950508446294321)
    ·
      refine ⟨327733028242462881334720741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436977370989950508446294321 327733028242462881334720741)
      ·
        refine ⟨61449942795461790250260139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327733028242462881334720741 61449942795461790250260139)
        ·
          refine ⟨92174914193192685375390209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61449942795461790250260139 92174914193192685375390209)
          ·
            refine ⟨69131185644894514031542657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92174914193192685375390209 69131185644894514031542657)
            ·
              refine ⟨51848389233670885523656993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69131185644894514031542657 51848389233670885523656993)
              ·
                refine ⟨38886291925253164142742745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51848389233670885523656993 38886291925253164142742745)
                ·
                  refine ⟨29164718943939873107057059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38886291925253164142742745 29164718943939873107057059)
                  ·
                    refine ⟨43747078415909809660585589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29164718943939873107057059 43747078415909809660585589)
                    ·
                      refine ⟨4101288601491544655679899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43747078415909809660585589 4101288601491544655679899)
                      ·
                        rfl

theorem cell23_7987231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7987231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987231 prefixEnd_7987231 := by exact prefixLift 7987231
  have htrace : WordTrace (prefixWord ++ tailWord_7987231) baseStart_7987231 baseEnd_7987231 := by
    simpa [prefixWord, tailWord_7987231, baseEnd_7987231] using wordTrace_append hprefix tailTrace_7987231
  have hstable : (prefixWord ++ tailWord_7987231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987231).length < 2 ^ (prefixWord ++ tailWord_7987231).sum := by decide
  have hdescent : baseEnd_7987231 < baseStart_7987231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987261 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7987261 : Nat := 118140960795 + 7987261 * 2 ^ 59
def prefixEnd_7987261 : Nat := 4983230072969 + 3 ^ 40 * 7987261 * 2
def baseEnd_7987261 : Nat := 4101304005911179538304761

theorem tailTrace_7987261 : CollatzResearch.WordTrace tailWord_7987261 prefixEnd_7987261 4101304005911179538304761 := by
  unfold tailWord_7987261
  simp only [CollatzResearch.WordTrace]
  refine ⟨291319341516524987421121637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194212894344349991614081091 291319341516524987421121637)
  ·
    refine ⟨54622376534348435141460307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291319341516524987421121637 54622376534348435141460307)
    ·
      refine ⟨81933564801522652712190461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54622376534348435141460307 81933564801522652712190461)
      ·
        refine ⟨30725086800570994767071423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81933564801522652712190461 30725086800570994767071423)
        ·
          refine ⟨46087630200856492150607135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30725086800570994767071423 46087630200856492150607135)
          ·
            refine ⟨69131445301284738225910703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46087630200856492150607135 69131445301284738225910703)
            ·
              refine ⟨103697167951927107338866055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69131445301284738225910703 103697167951927107338866055)
              ·
                refine ⟨155545751927890661008299083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103697167951927107338866055 155545751927890661008299083)
                ·
                  refine ⟨233318627891835991512448625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155545751927890661008299083 233318627891835991512448625)
                  ·
                    refine ⟨174988970918876993634336469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233318627891835991512448625 174988970918876993634336469)
                    ·
                      refine ⟨4101304005911179538304761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174988970918876993634336469 4101304005911179538304761)
                      ·
                        rfl

theorem cell23_7987261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7987261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987261 prefixEnd_7987261 := by exact prefixLift 7987261
  have htrace : WordTrace (prefixWord ++ tailWord_7987261) baseStart_7987261 baseEnd_7987261 := by
    simpa [prefixWord, tailWord_7987261, baseEnd_7987261] using wordTrace_append hprefix tailTrace_7987261
  have hstable : (prefixWord ++ tailWord_7987261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987261).length < 2 ^ (prefixWord ++ tailWord_7987261).sum := by decide
  have hdescent : baseEnd_7987261 < baseStart_7987261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987281 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_7987281 : Nat := 118140960795 + 7987281 * 2 ^ 59
def prefixEnd_7987281 : Nat := 4983230072969 + 3 ^ 40 * 7987281 * 2
def baseEnd_7987281 : Nat := 1367104758508089820018223

theorem tailTrace_7987281 : CollatzResearch.WordTrace tailWord_7987281 prefixEnd_7987281 1367104758508089820018223 := by
  unfold tailWord_7987281
  simp only [CollatzResearch.WordTrace]
  refine ⟨291320070976452530836849697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194213380650968353891233131 291320070976452530836849697)
  ·
    refine ⟨218490053232339398127637273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291320070976452530836849697 218490053232339398127637273)
    ·
      refine ⟨163867539924254548595727955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218490053232339398127637273 163867539924254548595727955)
      ·
        refine ⟨245801309886381822893591933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163867539924254548595727955 245801309886381822893591933)
        ·
          refine ⟨92175491207393183585096975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245801309886381822893591933 92175491207393183585096975)
          ·
            refine ⟨138263236811089775377645463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92175491207393183585096975 138263236811089775377645463)
            ·
              refine ⟨207394855216634663066468195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138263236811089775377645463 207394855216634663066468195)
              ·
                refine ⟨311092282824951994599702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207394855216634663066468195 311092282824951994599702293)
                ·
                  refine ⟨14582450757419624746861045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311092282824951994599702293 14582450757419624746861045)
                  ·
                    refine ⟨1367104758508089820018223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14582450757419624746861045 1367104758508089820018223)
                    ·
                      rfl

theorem cell23_7987281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_7987281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987281 prefixEnd_7987281 := by exact prefixLift 7987281
  have htrace : WordTrace (prefixWord ++ tailWord_7987281) baseStart_7987281 baseEnd_7987281 := by
    simpa [prefixWord, tailWord_7987281, baseEnd_7987281] using wordTrace_append hprefix tailTrace_7987281
  have hstable : (prefixWord ++ tailWord_7987281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987281).length < 2 ^ (prefixWord ++ tailWord_7987281).sum := by decide
  have hdescent : baseEnd_7987281 < baseStart_7987281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987328 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_7987328 : Nat := 118140960795 + 7987328 * 2 ^ 59
def prefixEnd_7987328 : Nat := 4983230072969 + 3 ^ 40 * 7987328 * 2
def baseEnd_7987328 : Nat := 1367112803038343592055651

theorem tailTrace_7987328 : CollatzResearch.WordTrace tailWord_7987328 prefixEnd_7987328 1367112803038343592055651 := by
  unfold tailWord_7987328
  simp only [CollatzResearch.WordTrace]
  refine ⟨145660892603641128931905319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194214523471521505242540425 145660892603641128931905319)
  ·
    refine ⟨218491338905461693397857979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145660892603641128931905319 218491338905461693397857979)
    ·
      refine ⟨327737008358192540096786969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218491338905461693397857979 327737008358192540096786969)
      ·
        refine ⟨245802756268644405072590227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327737008358192540096786969 245802756268644405072590227)
        ·
          refine ⟨368704134402966607608885341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245802756268644405072590227 368704134402966607608885341)
          ·
            refine ⟨138264050401112477853332003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368704134402966607608885341 138264050401112477853332003)
            ·
              refine ⟨207396075601668716779998005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138264050401112477853332003 207396075601668716779998005)
              ·
                refine ⟨19443382087656442198124813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207396075601668716779998005 19443382087656442198124813)
                ·
                  refine ⟨7291268282871165824296805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19443382087656442198124813 7291268282871165824296805)
                  ·
                    refine ⟨1367112803038343592055651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291268282871165824296805 1367112803038343592055651)
                    ·
                      rfl

theorem cell23_7987328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_7987328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987328 prefixEnd_7987328 := by exact prefixLift 7987328
  have htrace : WordTrace (prefixWord ++ tailWord_7987328) baseStart_7987328 baseEnd_7987328 := by
    simpa [prefixWord, tailWord_7987328, baseEnd_7987328] using wordTrace_append hprefix tailTrace_7987328
  have hstable : (prefixWord ++ tailWord_7987328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987328).length < 2 ^ (prefixWord ++ tailWord_7987328).sum := by decide
  have hdescent : baseEnd_7987328 < baseStart_7987328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987352 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7987352 : Nat := 118140960795 + 7987352 * 2 ^ 59
def prefixEnd_7987352 : Nat := 4983230072969 + 3 ^ 40 * 7987352 * 2
def baseEnd_7987352 : Nat := 4101350732650738682266843

theorem tailTrace_7987352 : CollatzResearch.WordTrace tailWord_7987352 prefixEnd_7987352 4101350732650738682266843 := by
  unfold tailWord_7987352
  simp only [CollatzResearch.WordTrace]
  refine ⟨145661330279597654981342155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194215107039463539975122873 145661330279597654981342155)
  ·
    refine ⟨218491995419396482472013233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145661330279597654981342155 218491995419396482472013233)
    ·
      refine ⟨163868996564547361854009925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218491995419396482472013233 163868996564547361854009925)
      ·
        refine ⟨30725436855852630347626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163868996564547361854009925 30725436855852630347626861)
        ·
          refine ⟨11522038820944736380360073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30725436855852630347626861 11522038820944736380360073)
          ·
            refine ⟨8641529115708552285270055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522038820944736380360073 8641529115708552285270055)
            ·
              refine ⟨12962293673562828427905083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641529115708552285270055 12962293673562828427905083)
              ·
                refine ⟨19443440510344242641857625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962293673562828427905083 19443440510344242641857625)
                ·
                  refine ⟨14582580382758181981393219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19443440510344242641857625 14582580382758181981393219)
                  ·
                    refine ⟨21873870574137272972089829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14582580382758181981393219 21873870574137272972089829)
                    ·
                      refine ⟨4101350732650738682266843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21873870574137272972089829 4101350732650738682266843)
                      ·
                        rfl

theorem cell23_7987352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7987352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987352 prefixEnd_7987352 := by exact prefixLift 7987352
  have htrace : WordTrace (prefixWord ++ tailWord_7987352) baseStart_7987352 baseEnd_7987352 := by
    simpa [prefixWord, tailWord_7987352, baseEnd_7987352] using wordTrace_append hprefix tailTrace_7987352
  have hstable : (prefixWord ++ tailWord_7987352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987352).length < 2 ^ (prefixWord ++ tailWord_7987352).sum := by decide
  have hdescent : baseEnd_7987352 < baseStart_7987352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987418 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_7987418 : Nat := 118140960795 + 7987418 * 2 ^ 59
def prefixEnd_7987418 : Nat := 4983230072969 + 3 ^ 40 * 7987418 * 2
def baseEnd_7987418 : Nat := 1367128207457978474680513

theorem tailTrace_7987418 : CollatzResearch.WordTrace tailWord_7987418 prefixEnd_7987418 1367128207457978474680513 := by
  unfold tailWord_7987418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72831266944239050808646727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194216711851304135489724605 72831266944239050808646727)
  ·
    refine ⟨109246900416358576212970091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72831266944239050808646727 109246900416358576212970091)
    ·
      refine ⟨163870350624537864319455137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109246900416358576212970091 163870350624537864319455137)
      ·
        refine ⟨122902762968403398239591353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163870350624537864319455137 122902762968403398239591353)
        ·
          refine ⟨92177072226302548679693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122902762968403398239591353 92177072226302548679693515)
          ·
            refine ⟨138265608339453823019540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92177072226302548679693515 138265608339453823019540273)
            ·
              refine ⟨103699206254590367264655205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138265608339453823019540273 103699206254590367264655205)
              ·
                refine ⟨19443601172735693862122851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103699206254590367264655205 19443601172735693862122851)
                ·
                  refine ⟨29165401759103540793184277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19443601172735693862122851 29165401759103540793184277)
                  ·
                    refine ⟨1367128207457978474680513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29165401759103540793184277 1367128207457978474680513)
                    ·
                      rfl

theorem cell23_7987418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_7987418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987418 prefixEnd_7987418 := by exact prefixLift 7987418
  have htrace : WordTrace (prefixWord ++ tailWord_7987418) baseStart_7987418 baseEnd_7987418 := by
    simpa [prefixWord, tailWord_7987418, baseEnd_7987418] using wordTrace_append hprefix tailTrace_7987418
  have hstable : (prefixWord ++ tailWord_7987418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987418).length < 2 ^ (prefixWord ++ tailWord_7987418).sum := by decide
  have hdescent : baseEnd_7987418 < baseStart_7987418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987425 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7987425 : Nat := 118140960795 + 7987425 * 2 ^ 59
def prefixEnd_7987425 : Nat := 4983230072969 + 3 ^ 40 * 7987425 * 2
def baseEnd_7987425 : Nat := 4101388216738516896654007

theorem tailTrace_7987425 : CollatzResearch.WordTrace tailWord_7987425 prefixEnd_7987425 4101388216738516896654007 := by
  unfold tailWord_7987425
  simp only [CollatzResearch.WordTrace]
  refine ⟨291325323087930843430091729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194216882058620562286727819 291325323087930843430091729)
  ·
    refine ⟨218493992315948132572568797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291325323087930843430091729 218493992315948132572568797)
    ·
      refine ⟨81935247118480549714713299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218493992315948132572568797 81935247118480549714713299)
      ·
        refine ⟨122902870677720824572069949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81935247118480549714713299 122902870677720824572069949)
        ·
          refine ⟨46088576504145309214526231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122902870677720824572069949 46088576504145309214526231)
          ·
            refine ⟨69132864756217963821789347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46088576504145309214526231 69132864756217963821789347)
            ·
              refine ⟨103699297134326945732684021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69132864756217963821789347 103699297134326945732684021)
              ·
                refine ⟨9721809106343151162439127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103699297134326945732684021 9721809106343151162439127)
                ·
                  refine ⟨14582713659514726743658691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721809106343151162439127 14582713659514726743658691)
                  ·
                    refine ⟨21874070489272090115488037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14582713659514726743658691 21874070489272090115488037)
                    ·
                      refine ⟨4101388216738516896654007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21874070489272090115488037 4101388216738516896654007)
                      ·
                        rfl

theorem cell23_7987425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7987425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987425 prefixEnd_7987425 := by exact prefixLift 7987425
  have htrace : WordTrace (prefixWord ++ tailWord_7987425) baseStart_7987425 baseEnd_7987425 := by
    simpa [prefixWord, tailWord_7987425, baseEnd_7987425] using wordTrace_append hprefix tailTrace_7987425
  have hstable : (prefixWord ++ tailWord_7987425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987425).length < 2 ^ (prefixWord ++ tailWord_7987425).sum := by decide
  have hdescent : baseEnd_7987425 < baseStart_7987425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987435 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 2, 4]
def baseStart_7987435 : Nat := 118140960795 + 7987435 * 2 ^ 59
def prefixEnd_7987435 : Nat := 4983230072969 + 3 ^ 40 * 7987435 * 2
def baseEnd_7987435 : Nat := 1367131117181687285842987

theorem tailTrace_7987435 : CollatzResearch.WordTrace tailWord_7987435 prefixEnd_7987435 1367131117181687285842987 := by
  unfold tailWord_7987435
  simp only [CollatzResearch.WordTrace]
  refine ⟨291325687817894615137955759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194217125211929743425303839 291325687817894615137955759)
  ·
    refine ⟨436988531726841922706933639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291325687817894615137955759 436988531726841922706933639)
    ·
      refine ⟨655482797590262884060400459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436988531726841922706933639 655482797590262884060400459)
      ·
        refine ⟨983224196385394326090600689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655482797590262884060400459 983224196385394326090600689)
        ·
          refine ⟨737418147289045744567950517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983224196385394326090600689 737418147289045744567950517)
          ·
            refine ⟨69132951308348038553245361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 737418147289045744567950517 69132951308348038553245361)
            ·
              refine ⟨51849713481261028914934021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69132951308348038553245361 51849713481261028914934021)
              ·
                refine ⟨9721821277736442921550129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51849713481261028914934021 9721821277736442921550129)
                ·
                  refine ⟨7291365958302332191162597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721821277736442921550129 7291365958302332191162597)
                  ·
                    refine ⟨1367131117181687285842987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291365958302332191162597 1367131117181687285842987)
                    ·
                      rfl

theorem cell23_7987435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 4].length) (baseStart_7987435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987435 prefixEnd_7987435 := by exact prefixLift 7987435
  have htrace : WordTrace (prefixWord ++ tailWord_7987435) baseStart_7987435 baseEnd_7987435 := by
    simpa [prefixWord, tailWord_7987435, baseEnd_7987435] using wordTrace_append hprefix tailTrace_7987435
  have hstable : (prefixWord ++ tailWord_7987435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987435).length < 2 ^ (prefixWord ++ tailWord_7987435).sum := by decide
  have hdescent : baseEnd_7987435 < baseStart_7987435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987452 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_7987452 : Nat := 118140960795 + 7987452 * 2 ^ 59
def prefixEnd_7987452 : Nat := 4983230072969 + 3 ^ 40 * 7987452 * 2
def baseEnd_7987452 : Nat := 1367134026905396097005461

theorem tailTrace_7987452 : CollatzResearch.WordTrace tailWord_7987452 prefixEnd_7987452 1367134026905396097005461 := by
  unfold tailWord_7987452
  simp only [CollatzResearch.WordTrace]
  refine ⟨145663153929416513520662305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194217538572555351360883073 145663153929416513520662305)
  ·
    refine ⟨109247365447062385140496729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145663153929416513520662305 109247365447062385140496729)
    ·
      refine ⟨81935524085296788855372547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109247365447062385140496729 81935524085296788855372547)
      ·
        refine ⟨122903286127945183283058821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81935524085296788855372547 122903286127945183283058821)
        ·
          refine ⟨23044366148989721865573529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122903286127945183283058821 23044366148989721865573529)
          ·
            refine ⟨17283274611742291399180147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23044366148989721865573529 17283274611742291399180147)
            ·
              refine ⟨25924911917613437098770221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17283274611742291399180147 25924911917613437098770221)
              ·
                refine ⟨9721841969105038912038833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25924911917613437098770221 9721841969105038912038833)
                ·
                  refine ⟨7291381476828779184029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721841969105038912038833 7291381476828779184029125)
                  ·
                    refine ⟨1367134026905396097005461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291381476828779184029125 1367134026905396097005461)
                    ·
                      rfl

theorem cell23_7987452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_7987452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987452 prefixEnd_7987452 := by exact prefixLift 7987452
  have htrace : WordTrace (prefixWord ++ tailWord_7987452) baseStart_7987452 baseEnd_7987452 := by
    simpa [prefixWord, tailWord_7987452, baseEnd_7987452] using wordTrace_append hprefix tailTrace_7987452
  have hstable : (prefixWord ++ tailWord_7987452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987452).length < 2 ^ (prefixWord ++ tailWord_7987452).sum := by decide
  have hdescent : baseEnd_7987452 < baseStart_7987452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987475 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 3]
def baseStart_7987475 : Nat := 118140960795 + 7987475 * 2 ^ 59
def prefixEnd_7987475 : Nat := 4983230072969 + 3 ^ 40 * 7987475 * 2
def baseEnd_7987475 : Nat := 4101413890771241701028777

theorem tailTrace_7987475 : CollatzResearch.WordTrace tailWord_7987475 prefixEnd_7987475 4101413890771241701028777 := by
  unfold tailWord_7987475
  simp only [CollatzResearch.WordTrace]
  refine ⟨291327146737749701969411879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194218097825166467979607919 291327146737749701969411879)
  ·
    refine ⟨436990720106624552954117819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291327146737749701969411879 436990720106624552954117819)
    ·
      refine ⟨655486080159936829431176729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436990720106624552954117819 655486080159936829431176729)
      ·
        refine ⟨491614560119952622073382547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655486080159936829431176729 491614560119952622073382547)
        ·
          refine ⟨737421840179928933110073821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491614560119952622073382547 737421840179928933110073821)
          ·
            refine ⟨276533190067473349916277683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 737421840179928933110073821 276533190067473349916277683)
            ·
              refine ⟨414799785101210024874416525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276533190067473349916277683 414799785101210024874416525)
              ·
                refine ⟨155549919412953759327906197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414799785101210024874416525 155549919412953759327906197)
                ·
                  refine ⟨7291402472482207468495603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155549919412953759327906197 7291402472482207468495603)
                  ·
                    refine ⟨10937103708723311202743405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291402472482207468495603 10937103708723311202743405)
                    ·
                      refine ⟨4101413890771241701028777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937103708723311202743405 4101413890771241701028777)
                      ·
                        rfl

theorem cell23_7987475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_7987475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987475 prefixEnd_7987475 := by exact prefixLift 7987475
  have htrace : WordTrace (prefixWord ++ tailWord_7987475) baseStart_7987475 baseEnd_7987475 := by
    simpa [prefixWord, tailWord_7987475, baseEnd_7987475] using wordTrace_append hprefix tailTrace_7987475
  have hstable : (prefixWord ++ tailWord_7987475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987475).length < 2 ^ (prefixWord ++ tailWord_7987475).sum := by decide
  have hdescent : baseEnd_7987475 < baseStart_7987475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987479 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7987479 : Nat := 118140960795 + 7987479 * 2 ^ 59
def prefixEnd_7987479 : Nat := 4983230072969 + 3 ^ 40 * 7987479 * 2
def baseEnd_7987479 : Nat := 4101415944693859685378759

theorem tailTrace_7987479 : CollatzResearch.WordTrace tailWord_7987479 prefixEnd_7987479 4101415944693859685378759 := by
  unfold tailWord_7987479
  simp only [CollatzResearch.WordTrace]
  refine ⟨291327292629735210652557491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194218195086490140435038327 291327292629735210652557491)
  ·
    refine ⟨436990938944602815978836237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291327292629735210652557491 436990938944602815978836237)
    ·
      refine ⟨163871602104226055992063589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 436990938944602815978836237 163871602104226055992063589)
      ·
        refine ⟨30725925394542385498511923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163871602104226055992063589 30725925394542385498511923)
        ·
          refine ⟨46088888091813578247767885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30725925394542385498511923 46088888091813578247767885)
          ·
            refine ⟨17283333034430091842912957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46088888091813578247767885 17283333034430091842912957)
            ·
              refine ⟨6481249887911284441092359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17283333034430091842912957 6481249887911284441092359)
              ·
                refine ⟨9721874831866926661638539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481249887911284441092359 9721874831866926661638539)
                ·
                  refine ⟨14582812247800389992457809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721874831866926661638539 14582812247800389992457809)
                  ·
                    refine ⟨10937109185850292494343357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14582812247800389992457809 10937109185850292494343357)
                    ·
                      refine ⟨4101415944693859685378759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937109185850292494343357 4101415944693859685378759)
                      ·
                        rfl

theorem cell23_7987479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7987479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987479 prefixEnd_7987479 := by exact prefixLift 7987479
  have htrace : WordTrace (prefixWord ++ tailWord_7987479) baseStart_7987479 baseEnd_7987479 := by
    simpa [prefixWord, tailWord_7987479, baseEnd_7987479] using wordTrace_append hprefix tailTrace_7987479
  have hstable : (prefixWord ++ tailWord_7987479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987479).length < 2 ^ (prefixWord ++ tailWord_7987479).sum := by decide
  have hdescent : baseEnd_7987479 < baseStart_7987479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987486 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7987486 : Nat := 118140960795 + 7987486 * 2 ^ 59
def prefixEnd_7987486 : Nat := 4983230072969 + 3 ^ 40 * 7987486 * 2
def baseEnd_7987486 : Nat := 1367139846352813719330409

theorem tailTrace_7987486 : CollatzResearch.WordTrace tailWord_7987486 prefixEnd_7987486 1367139846352813719330409 := by
  unfold tailWord_7987486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415943492588731356007789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194218365293806567232041541 36415943492588731356007789)
  ·
    refine ⟨13655978809720774258502921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36415943492588731356007789 13655978809720774258502921)
    ·
      refine ⟨10241984107290580693877191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13655978809720774258502921 10241984107290580693877191)
      ·
        refine ⟨15362976160935871040815787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241984107290580693877191 15362976160935871040815787)
        ·
          refine ⟨23044464241403806561223681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15362976160935871040815787 23044464241403806561223681)
          ·
            refine ⟨17283348181052854920917761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23044464241403806561223681 17283348181052854920917761)
            ·
              refine ⟨12962511135789641190688321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17283348181052854920917761 12962511135789641190688321)
              ·
                refine ⟨9721883351842230893016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962511135789641190688321 9721883351842230893016241)
                ·
                  refine ⟨7291412513881673169762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721883351842230893016241 7291412513881673169762181)
                  ·
                    refine ⟨1367139846352813719330409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291412513881673169762181 1367139846352813719330409)
                    ·
                      rfl

theorem cell23_7987486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7987486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987486 prefixEnd_7987486 := by exact prefixLift 7987486
  have htrace : WordTrace (prefixWord ++ tailWord_7987486) baseStart_7987486 baseEnd_7987486 := by
    simpa [prefixWord, tailWord_7987486, baseEnd_7987486] using wordTrace_append hprefix tailTrace_7987486
  have hstable : (prefixWord ++ tailWord_7987486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987486).length < 2 ^ (prefixWord ++ tailWord_7987486).sum := by decide
  have hdescent : baseEnd_7987486 < baseStart_7987486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987532 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7987532 : Nat := 118140960795 + 7987532 * 2 ^ 59
def prefixEnd_7987532 : Nat := 4983230072969 + 3 ^ 40 * 7987532 * 2
def baseEnd_7987532 : Nat := 4101443159168547978016015

theorem tailTrace_7987532 : CollatzResearch.WordTrace tailWord_7987532 prefixEnd_7987532 4101443159168547978016015 := by
  unfold tailWord_7987532
  simp only [CollatzResearch.WordTrace]
  refine ⟨145664612849271600352118425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194219483799028800469491233 145664612849271600352118425)
  ·
    refine ⟨109248459636953700264088819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145664612849271600352118425 109248459636953700264088819)
    ·
      refine ⟨163872689455430550396133229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109248459636953700264088819 163872689455430550396133229)
      ·
        refine ⟨61452258545786456398549961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163872689455430550396133229 61452258545786456398549961)
        ·
          refine ⟨46089193909339842298912471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61452258545786456398549961 46089193909339842298912471)
          ·
            refine ⟨69133790864009763448368707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46089193909339842298912471 69133790864009763448368707)
            ·
              refine ⟨103700686296014645172553061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69133790864009763448368707 103700686296014645172553061)
              ·
                refine ⟨19443878680502745969853699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103700686296014645172553061 19443878680502745969853699)
                ·
                  refine ⟨29165818020754118954780549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19443878680502745969853699 29165818020754118954780549)
                  ·
                    refine ⟨5468590878891397304021353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29165818020754118954780549 5468590878891397304021353)
                    ·
                      refine ⟨4101443159168547978016015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468590878891397304021353 4101443159168547978016015)
                      ·
                        rfl

theorem cell23_7987532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7987532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987532 prefixEnd_7987532 := by exact prefixLift 7987532
  have htrace : WordTrace (prefixWord ++ tailWord_7987532) baseStart_7987532 baseEnd_7987532 := by
    simpa [prefixWord, tailWord_7987532, baseEnd_7987532] using wordTrace_append hprefix tailTrace_7987532
  have hstable : (prefixWord ++ tailWord_7987532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987532).length < 2 ^ (prefixWord ++ tailWord_7987532).sum := by decide
  have hdescent : baseEnd_7987532 < baseStart_7987532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987536 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2]
def baseStart_7987536 : Nat := 118140960795 + 7987536 * 2 ^ 59
def prefixEnd_7987536 : Nat := 4983230072969 + 3 ^ 40 * 7987536 * 2
def baseEnd_7987536 : Nat := 4101445213091165962365997

theorem tailTrace_7987536 : CollatzResearch.WordTrace tailWord_7987536 prefixEnd_7987536 4101445213091165962365997 := by
  unfold tailWord_7987536
  simp only [CollatzResearch.WordTrace]
  refine ⟨145664685795264354693691231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194219581060352472924921641 145664685795264354693691231)
  ·
    refine ⟨218497028692896532040536847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145664685795264354693691231 218497028692896532040536847)
    ·
      refine ⟨327745543039344798060805271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218497028692896532040536847 327745543039344798060805271)
      ·
        refine ⟨491618314559017197091207907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327745543039344798060805271 491618314559017197091207907)
        ·
          refine ⟨737427471838525795636811861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491618314559017197091207907 737427471838525795636811861)
          ·
            refine ⟨8641728185607724167618889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 737427471838525795636811861 8641728185607724167618889)
            ·
              refine ⟨6481296139205793125714167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8641728185607724167618889 6481296139205793125714167)
              ·
                refine ⟨9721944208808689688571251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481296139205793125714167 9721944208808689688571251)
                ·
                  refine ⟨14582916313213034532856877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721944208808689688571251 14582916313213034532856877)
                  ·
                    refine ⟨5468593617454887949821329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14582916313213034532856877 5468593617454887949821329)
                    ·
                      refine ⟨4101445213091165962365997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468593617454887949821329 4101445213091165962365997)
                      ·
                        rfl

theorem cell23_7987536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2].length) (baseStart_7987536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987536 prefixEnd_7987536 := by exact prefixLift 7987536
  have htrace : WordTrace (prefixWord ++ tailWord_7987536) baseStart_7987536 baseEnd_7987536 := by
    simpa [prefixWord, tailWord_7987536, baseEnd_7987536] using wordTrace_append hprefix tailTrace_7987536
  have hstable : (prefixWord ++ tailWord_7987536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987536).length < 2 ^ (prefixWord ++ tailWord_7987536).sum := by decide
  have hdescent : baseEnd_7987536 < baseStart_7987536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987555 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 7]
def baseStart_7987555 : Nat := 118140960795 + 7987555 * 2 ^ 59
def prefixEnd_7987555 : Nat := 4983230072969 + 3 ^ 40 * 7987555 * 2
def baseEnd_7987555 : Nat := 455717218802622376447601

theorem tailTrace_7987555 : CollatzResearch.WordTrace tailWord_7987555 prefixEnd_7987555 455717218802622376447601 := by
  unfold tailWord_7987555
  simp only [CollatzResearch.WordTrace]
  refine ⟨291330064577459875632324119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194220043051639917088216079 291330064577459875632324119)
  ·
    refine ⟨436995096866189813448486179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291330064577459875632324119 436995096866189813448486179)
    ·
      refine ⟨655492645299284720172729269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436995096866189813448486179 655492645299284720172729269)
      ·
        refine ⟨61452435496807942516193369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 655492645299284720172729269 61452435496807942516193369)
        ·
          refine ⟨46089326622605956887145027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61452435496807942516193369 46089326622605956887145027)
          ·
            refine ⟨69133989933908935330717541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46089326622605956887145027 69133989933908935330717541)
            ·
              refine ⟨12962623112607925374509539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69133989933908935330717541 12962623112607925374509539)
              ·
                refine ⟨19443934668911888061764309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962623112607925374509539 19443934668911888061764309)
                ·
                  refine ⟨455717218802622376447601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19443934668911888061764309 455717218802622376447601)
                  ·
                    rfl

theorem cell23_7987555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 7].length) (baseStart_7987555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987555 prefixEnd_7987555 := by exact prefixLift 7987555
  have htrace : WordTrace (prefixWord ++ tailWord_7987555) baseStart_7987555 baseEnd_7987555 := by
    simpa [prefixWord, tailWord_7987555, baseEnd_7987555] using wordTrace_append hprefix tailTrace_7987555
  have hstable : (prefixWord ++ tailWord_7987555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987555).length < 2 ^ (prefixWord ++ tailWord_7987555).sum := by decide
  have hdescent : baseEnd_7987555 < baseStart_7987555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987562 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7987562 : Nat := 118140960795 + 7987562 * 2 ^ 59
def prefixEnd_7987562 : Nat := 4983230072969 + 3 ^ 40 * 7987562 * 2
def baseEnd_7987562 : Nat := 4101458563588182860640877

theorem tailTrace_7987562 : CollatzResearch.WordTrace tailWord_7987562 prefixEnd_7987562 4101458563588182860640877 := by
  unfold tailWord_7987562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72832579972108628956957235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194220213258956343885219293 72832579972108628956957235)
  ·
    refine ⟨109248869958162943435435853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72832579972108628956957235 109248869958162943435435853)
    ·
      refine ⟨40968326234311103788288445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109248869958162943435435853 40968326234311103788288445)
      ·
        refine ⟨15363122337866663920608167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40968326234311103788288445 15363122337866663920608167)
        ·
          refine ⟨23044683506799995880912251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363122337866663920608167 23044683506799995880912251)
          ·
            refine ⟨34567025260199993821368377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23044683506799995880912251 34567025260199993821368377)
            ·
              refine ⟨25925268945149995366026283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34567025260199993821368377 25925268945149995366026283)
              ·
                refine ⟨38887903417724993049039425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25925268945149995366026283 38887903417724993049039425)
                ·
                  refine ⟨29165927563293744786779569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38887903417724993049039425 29165927563293744786779569)
                  ·
                    refine ⟨21874445672470308590084677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29165927563293744786779569 21874445672470308590084677)
                    ·
                      refine ⟨4101458563588182860640877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21874445672470308590084677 4101458563588182860640877)
                      ·
                        rfl

theorem cell23_7987562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7987562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987562 prefixEnd_7987562 := by exact prefixLift 7987562
  have htrace : WordTrace (prefixWord ++ tailWord_7987562) baseStart_7987562 baseEnd_7987562 := by
    simpa [prefixWord, tailWord_7987562, baseEnd_7987562] using wordTrace_append hprefix tailTrace_7987562
  have hstable : (prefixWord ++ tailWord_7987562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987562).length < 2 ^ (prefixWord ++ tailWord_7987562).sum := by decide
  have hdescent : baseEnd_7987562 < baseStart_7987562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987617 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7987617 : Nat := 118140960795 + 7987617 * 2 ^ 59
def prefixEnd_7987617 : Nat := 4983230072969 + 3 ^ 40 * 7987617 * 2
def baseEnd_7987617 : Nat := 4101486805024180145453125

theorem tailTrace_7987617 : CollatzResearch.WordTrace tailWord_7987617 prefixEnd_7987617 4101486805024180145453125 := by
  unfold tailWord_7987617
  simp only [CollatzResearch.WordTrace]
  refine ⟨291332325903235260221081105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194221550602156840147387403 291332325903235260221081105)
  ·
    refine ⟨218499244427426445165810829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291332325903235260221081105 218499244427426445165810829)
    ·
      refine ⟨81937216660284916937179061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218499244427426445165810829 81937216660284916937179061)
      ·
        refine ⟨7681614061901710962860537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81937216660284916937179061 7681614061901710962860537)
        ·
          refine ⟨5761210546426283222145403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7681614061901710962860537 5761210546426283222145403)
          ·
            refine ⟨8641815819639424833218105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761210546426283222145403 8641815819639424833218105)
            ·
              refine ⟨6481361864729568624913579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8641815819639424833218105 6481361864729568624913579)
              ·
                refine ⟨9722042797094352937370369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481361864729568624913579 9722042797094352937370369)
                ·
                  refine ⟨7291532097820764703027777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722042797094352937370369 7291532097820764703027777)
                  ·
                    refine ⟨5468649073365573527270833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291532097820764703027777 5468649073365573527270833)
                    ·
                      refine ⟨4101486805024180145453125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468649073365573527270833 4101486805024180145453125)
                      ·
                        rfl

theorem cell23_7987617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7987617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987617 prefixEnd_7987617 := by exact prefixLift 7987617
  have htrace : WordTrace (prefixWord ++ tailWord_7987617) baseStart_7987617 baseEnd_7987617 := by
    simpa [prefixWord, tailWord_7987617, baseEnd_7987617] using wordTrace_append hprefix tailTrace_7987617
  have hstable : (prefixWord ++ tailWord_7987617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987617).length < 2 ^ (prefixWord ++ tailWord_7987617).sum := by decide
  have hdescent : baseEnd_7987617 < baseStart_7987617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987625 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_7987625 : Nat := 118140960795 + 7987625 * 2 ^ 59
def prefixEnd_7987625 : Nat := 4983230072969 + 3 ^ 40 * 7987625 * 2
def baseEnd_7987625 : Nat := 4101490912869416114153087

theorem tailTrace_7987625 : CollatzResearch.WordTrace tailWord_7987625 prefixEnd_7987625 4101490912869416114153087 := by
  unfold tailWord_7987625
  simp only [CollatzResearch.WordTrace]
  refine ⟨291332617687206277587372329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194221745124804185058248219 291332617687206277587372329)
  ·
    refine ⟨218499463265404708190529247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291332617687206277587372329 218499463265404708190529247)
    ·
      refine ⟨327749194898107062285793871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218499463265404708190529247 327749194898107062285793871)
      ·
        refine ⟨491623792347160593428690807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327749194898107062285793871 491623792347160593428690807)
        ·
          refine ⟨737435688520740890143036211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491623792347160593428690807 737435688520740890143036211)
          ·
            refine ⟨1106153532781111335214554317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737435688520740890143036211 1106153532781111335214554317)
            ·
              refine ⟨414807574792916750705457869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106153532781111335214554317 414807574792916750705457869)
              ·
                refine ⟨155552840547343781514546701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414807574792916750705457869 155552840547343781514546701)
                ·
                  refine ⟨58332315205253918067955013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155552840547343781514546701 58332315205253918067955013)
                  ·
                    refine ⟨10937309100985109637741565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58332315205253918067955013 10937309100985109637741565)
                    ·
                      refine ⟨4101490912869416114153087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937309100985109637741565 4101490912869416114153087)
                      ·
                        rfl

theorem cell23_7987625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_7987625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987625 prefixEnd_7987625 := by exact prefixLift 7987625
  have htrace : WordTrace (prefixWord ++ tailWord_7987625) baseStart_7987625 baseEnd_7987625 := by
    simpa [prefixWord, tailWord_7987625, baseEnd_7987625] using wordTrace_append hprefix tailTrace_7987625
  have hstable : (prefixWord ++ tailWord_7987625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987625).length < 2 ^ (prefixWord ++ tailWord_7987625).sum := by decide
  have hdescent : baseEnd_7987625 < baseStart_7987625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987692 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_7987692 : Nat := 118140960795 + 7987692 * 2 ^ 59
def prefixEnd_7987692 : Nat := 4983230072969 + 3 ^ 40 * 7987692 * 2
def baseEnd_7987692 : Nat := 1367175105357755784005093

theorem tailTrace_7987692 : CollatzResearch.WordTrace tailWord_7987692 prefixEnd_7987692 1367175105357755784005093 := by
  unfold tailWord_7987692
  simp only [CollatzResearch.WordTrace]
  refine ⟨145667530688981774015030665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194223374251975698686707553 145667530688981774015030665)
  ·
    refine ⟨109250648016736330511272999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145667530688981774015030665 109250648016736330511272999)
    ·
      refine ⟨163875972025104495766909499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109250648016736330511272999 163875972025104495766909499)
      ·
        refine ⟨245813958037656743650364249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163875972025104495766909499 245813958037656743650364249)
        ·
          refine ⟨184360468528242557737773187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245813958037656743650364249 184360468528242557737773187)
          ·
            refine ⟨276540702792363836606659781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184360468528242557737773187 276540702792363836606659781)
            ·
              refine ⟨51851381773568219363748709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276540702792363836606659781 51851381773568219363748709)
              ·
                refine ⟨9722134082544041130702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51851381773568219363748709 9722134082544041130702883)
                ·
                  refine ⟨14583201123816061696054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722134082544041130702883 14583201123816061696054325)
                  ·
                    refine ⟨1367175105357755784005093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14583201123816061696054325 1367175105357755784005093)
                    ·
                      rfl

theorem cell23_7987692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_7987692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987692 prefixEnd_7987692 := by exact prefixLift 7987692
  have htrace : WordTrace (prefixWord ++ tailWord_7987692) baseStart_7987692 baseEnd_7987692 := by
    simpa [prefixWord, tailWord_7987692, baseEnd_7987692] using wordTrace_append hprefix tailTrace_7987692
  have hstable : (prefixWord ++ tailWord_7987692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987692).length < 2 ^ (prefixWord ++ tailWord_7987692).sum := by decide
  have hdescent : baseEnd_7987692 < baseStart_7987692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987712 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2]
def baseStart_7987712 : Nat := 118140960795 + 7987712 * 2 ^ 59
def prefixEnd_7987712 : Nat := 4983230072969 + 3 ^ 40 * 7987712 * 2
def baseEnd_7987712 : Nat := 4101535585686357273765187

theorem tailTrace_7987712 : CollatzResearch.WordTrace tailWord_7987712 prefixEnd_7987712 4101535585686357273765187 := by
  unfold tailWord_7987712
  simp only [CollatzResearch.WordTrace]
  refine ⟨145667895418945545722894695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194223860558594060963859593 145667895418945545722894695)
  ·
    refine ⟨218501843128418318584342043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145667895418945545722894695 218501843128418318584342043)
    ·
      refine ⟨327752764692627477876513065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218501843128418318584342043 327752764692627477876513065)
      ·
        refine ⟨245814573519470608407384799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327752764692627477876513065 245814573519470608407384799)
        ·
          refine ⟨368721860279205912611077199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245814573519470608407384799 368721860279205912611077199)
          ·
            refine ⟨553082790418808868916615799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368721860279205912611077199 553082790418808868916615799)
            ·
              refine ⟨829624185628213303374923699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553082790418808868916615799 829624185628213303374923699)
              ·
                refine ⟨1244436278442319955062385549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829624185628213303374923699 1244436278442319955062385549)
                ·
                  refine ⟨466663604415869983148394581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1244436278442319955062385549 466663604415869983148394581)
                  ·
                    refine ⟨5468714114248476365020249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 466663604415869983148394581 5468714114248476365020249)
                    ·
                      refine ⟨4101535585686357273765187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468714114248476365020249 4101535585686357273765187)
                      ·
                        rfl

theorem cell23_7987712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_7987712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987712 prefixEnd_7987712 := by exact prefixLift 7987712
  have htrace : WordTrace (prefixWord ++ tailWord_7987712) baseStart_7987712 baseEnd_7987712 := by
    simpa [prefixWord, tailWord_7987712, baseEnd_7987712] using wordTrace_append hprefix tailTrace_7987712
  have hstable : (prefixWord ++ tailWord_7987712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987712).length < 2 ^ (prefixWord ++ tailWord_7987712).sum := by decide
  have hdescent : baseEnd_7987712 < baseStart_7987712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987749 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_7987749 : Nat := 118140960795 + 7987749 * 2 ^ 59
def prefixEnd_7987749 : Nat := 4983230072969 + 3 ^ 40 * 7987749 * 2
def baseEnd_7987749 : Nat := 4101554584470573629002517

theorem tailTrace_7987749 : CollatzResearch.WordTrace tailWord_7987749 prefixEnd_7987749 4101554584470573629002517 := by
  unfold tailWord_7987749
  simp only [CollatzResearch.WordTrace]
  refine ⟨291337140338757046764886301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194224760225838031176590867 291337140338757046764886301)
  ·
    refine ⟨109251427627033892536832363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291337140338757046764886301 109251427627033892536832363)
    ·
      refine ⟨163877141440550838805248545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109251427627033892536832363 163877141440550838805248545)
      ·
        refine ⟨122907856080413129103936409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163877141440550838805248545 122907856080413129103936409)
        ·
          refine ⟨92180892060309846827952307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122907856080413129103936409 92180892060309846827952307)
          ·
            refine ⟨138271338090464770241928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92180892060309846827952307 138271338090464770241928461)
            ·
              refine ⟨51851751783924288840723173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138271338090464770241928461 51851751783924288840723173)
              ·
                refine ⟨9722203459485804157635595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51851751783924288840723173 9722203459485804157635595)
                ·
                  refine ⟨14583305189228706236453393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722203459485804157635595 14583305189228706236453393)
                  ·
                    refine ⟨10937478891921529677340045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14583305189228706236453393 10937478891921529677340045)
                    ·
                      refine ⟨4101554584470573629002517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937478891921529677340045 4101554584470573629002517)
                      ·
                        rfl

theorem cell23_7987749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_7987749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987749 prefixEnd_7987749 := by exact prefixLift 7987749
  have htrace : WordTrace (prefixWord ++ tailWord_7987749) baseStart_7987749 baseEnd_7987749 := by
    simpa [prefixWord, tailWord_7987749, baseEnd_7987749] using wordTrace_append hprefix tailTrace_7987749
  have hstable : (prefixWord ++ tailWord_7987749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987749).length < 2 ^ (prefixWord ++ tailWord_7987749).sum := by decide
  have hdescent : baseEnd_7987749 < baseStart_7987749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_7987755 : Nat := 118140960795 + 7987755 * 2 ^ 59
def prefixEnd_7987755 : Nat := 4983230072969 + 3 ^ 40 * 7987755 * 2
def baseEnd_7987755 : Nat := 4101557665354500605527489

theorem tailTrace_7987755 : CollatzResearch.WordTrace tailWord_7987755 prefixEnd_7987755 4101557665354500605527489 := by
  unfold tailWord_7987755
  simp only [CollatzResearch.WordTrace]
  refine ⟨291337359176735309789604719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194224906117823539859736479 291337359176735309789604719)
  ·
    refine ⟨437006038765102964684407079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291337359176735309789604719 437006038765102964684407079)
    ·
      refine ⟨655509058147654447026610619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437006038765102964684407079 655509058147654447026610619)
      ·
        refine ⟨983263587221481670539915929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655509058147654447026610619 983263587221481670539915929)
        ·
          refine ⟨737447690416111252904936947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983263587221481670539915929 737447690416111252904936947)
          ·
            refine ⟨1106171535624166879357405421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737447690416111252904936947 1106171535624166879357405421)
            ·
              refine ⟨414814325859062579759027033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106171535624166879357405421 414814325859062579759027033)
              ·
                refine ⟨311110744394296934819270275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414814325859062579759027033 311110744394296934819270275)
                ·
                  refine ⟨466666116591445402228905413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311110744394296934819270275 466666116591445402228905413)
                  ·
                    refine ⟨87499896860896012917919765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466666116591445402228905413 87499896860896012917919765)
                    ·
                      refine ⟨4101557665354500605527489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87499896860896012917919765 4101557665354500605527489)
                      ·
                        rfl

theorem cell23_7987755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_7987755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987755 prefixEnd_7987755 := by exact prefixLift 7987755
  have htrace : WordTrace (prefixWord ++ tailWord_7987755) baseStart_7987755 baseEnd_7987755 := by
    simpa [prefixWord, tailWord_7987755, baseEnd_7987755] using wordTrace_append hprefix tailTrace_7987755
  have hstable : (prefixWord ++ tailWord_7987755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987755).length < 2 ^ (prefixWord ++ tailWord_7987755).sum := by decide
  have hdescent : baseEnd_7987755 < baseStart_7987755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987766 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_7987766 : Nat := 118140960795 + 7987766 * 2 ^ 59
def prefixEnd_7987766 : Nat := 4983230072969 + 3 ^ 40 * 7987766 * 2
def baseEnd_7987766 : Nat := 4101563313641700062489939

theorem tailTrace_7987766 : CollatzResearch.WordTrace tailWord_7987766 prefixEnd_7987766 4101563313641700062489939 := by
  unfold tailWord_7987766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208610023730966166765947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194225173586463639112170101 18208610023730966166765947)
  ·
    refine ⟨27312915035596449250148921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18208610023730966166765947 27312915035596449250148921)
    ·
      refine ⟨20484686276697336937611691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27312915035596449250148921 20484686276697336937611691)
      ·
        refine ⟨30727029415046005406417537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20484686276697336937611691 30727029415046005406417537)
        ·
          refine ⟨23045272061284504054813153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30727029415046005406417537 23045272061284504054813153)
          ·
            refine ⟨17283954045963378041109865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23045272061284504054813153 17283954045963378041109865)
            ·
              refine ⟨12962965534472533530832399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17283954045963378041109865 12962965534472533530832399)
              ·
                refine ⟨19444448301708800296248599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962965534472533530832399 19444448301708800296248599)
                ·
                  refine ⟨29166672452563200444372899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19444448301708800296248599 29166672452563200444372899)
                  ·
                    refine ⟨43750008678844800666559349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29166672452563200444372899 43750008678844800666559349)
                    ·
                      refine ⟨4101563313641700062489939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43750008678844800666559349 4101563313641700062489939)
                      ·
                        rfl

theorem cell23_7987766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_7987766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987766 prefixEnd_7987766 := by exact prefixLift 7987766
  have htrace : WordTrace (prefixWord ++ tailWord_7987766) baseStart_7987766 baseEnd_7987766 := by
    simpa [prefixWord, tailWord_7987766, baseEnd_7987766] using wordTrace_append hprefix tailTrace_7987766
  have hstable : (prefixWord ++ tailWord_7987766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987766).length < 2 ^ (prefixWord ++ tailWord_7987766).sum := by decide
  have hdescent : baseEnd_7987766 < baseStart_7987766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987830 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7987830 : Nat := 118140960795 + 7987830 * 2 ^ 59
def prefixEnd_7987830 : Nat := 4983230072969 + 3 ^ 40 * 7987830 * 2
def baseEnd_7987830 : Nat := 4101596176403587812089645

theorem tailTrace_7987830 : CollatzResearch.WordTrace tailWord_7987830 prefixEnd_7987830 4101596176403587812089645 := by
  unfold tailWord_7987830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208755915716474849911559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194226729767642398399056629 18208755915716474849911559)
  ·
    refine ⟨27313133873574712274867339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18208755915716474849911559 27313133873574712274867339)
    ·
      refine ⟨40969700810362068412301009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27313133873574712274867339 40969700810362068412301009)
      ·
        refine ⟨30727275607771551309225757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40969700810362068412301009 30727275607771551309225757)
        ·
          refine ⟨11522728352914331740959659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30727275607771551309225757 11522728352914331740959659)
          ·
            refine ⟨17284092529371497611439489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522728352914331740959659 17284092529371497611439489)
            ·
              refine ⟨12963069397028623208579617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17284092529371497611439489 12963069397028623208579617)
              ·
                refine ⟨9722302047771467406434713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963069397028623208579617 9722302047771467406434713)
                ·
                  refine ⟨7291726535828600554826035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722302047771467406434713 7291726535828600554826035)
                  ·
                    refine ⟨10937589803742900832239053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291726535828600554826035 10937589803742900832239053)
                    ·
                      refine ⟨4101596176403587812089645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937589803742900832239053 4101596176403587812089645)
                      ·
                        rfl

theorem cell23_7987830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7987830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987830 prefixEnd_7987830 := by exact prefixLift 7987830
  have htrace : WordTrace (prefixWord ++ tailWord_7987830) baseStart_7987830 baseEnd_7987830 := by
    simpa [prefixWord, tailWord_7987830, baseEnd_7987830] using wordTrace_append hprefix tailTrace_7987830
  have hstable : (prefixWord ++ tailWord_7987830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987830).length < 2 ^ (prefixWord ++ tailWord_7987830).sum := by decide
  have hdescent : baseEnd_7987830 < baseStart_7987830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987832 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_7987832 : Nat := 118140960795 + 7987832 * 2 ^ 59
def prefixEnd_7987832 : Nat := 4983230072969 + 3 ^ 40 * 7987832 * 2
def baseEnd_7987832 : Nat := 4101597203364896804264635

theorem tailTrace_7987832 : CollatzResearch.WordTrace tailWord_7987832 prefixEnd_7987832 4101597203364896804264635 := by
  unfold tailWord_7987832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145670083798728175970078875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194226778398304234626771833 145670083798728175970078875)
  ·
    refine ⟨218505125698092263955118313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145670083798728175970078875 218505125698092263955118313)
    ·
      refine ⟨163878844273569197966338735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218505125698092263955118313 163878844273569197966338735)
      ·
        refine ⟨245818266410353796949508103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163878844273569197966338735 245818266410353796949508103)
        ·
          refine ⟨368727399615530695424262155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245818266410353796949508103 368727399615530695424262155)
          ·
            refine ⟨553091099423296043136393233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368727399615530695424262155 553091099423296043136393233)
            ·
              refine ⟨414818324567472032352294925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553091099423296043136393233 414818324567472032352294925)
              ·
                refine ⟨155556871712802012132110597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414818324567472032352294925 155556871712802012132110597)
                ·
                  refine ⟨29166913446150377274770737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155556871712802012132110597 29166913446150377274770737)
                  ·
                    refine ⟨21875185084612782956078053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29166913446150377274770737 21875185084612782956078053)
                    ·
                      refine ⟨4101597203364896804264635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21875185084612782956078053 4101597203364896804264635)
                      ·
                        rfl

theorem cell23_7987832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_7987832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987832 prefixEnd_7987832 := by exact prefixLift 7987832
  have htrace : WordTrace (prefixWord ++ tailWord_7987832) baseStart_7987832 baseEnd_7987832 := by
    simpa [prefixWord, tailWord_7987832, baseEnd_7987832] using wordTrace_append hprefix tailTrace_7987832
  have hstable : (prefixWord ++ tailWord_7987832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987832).length < 2 ^ (prefixWord ++ tailWord_7987832).sum := by decide
  have hdescent : baseEnd_7987832 < baseStart_7987832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987836 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_7987836 : Nat := 118140960795 + 7987836 * 2 ^ 59
def prefixEnd_7987836 : Nat := 4983230072969 + 3 ^ 40 * 7987836 * 2
def baseEnd_7987836 : Nat := 4101599257287514788614617

theorem tailTrace_7987836 : CollatzResearch.WordTrace tailWord_7987836 prefixEnd_7987836 4101599257287514788614617 := by
  unfold tailWord_7987836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145670156744720930311651681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194226875659627907082202241 145670156744720930311651681)
  ·
    refine ⟨109252617558540697733738761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145670156744720930311651681 109252617558540697733738761)
    ·
      refine ⟨81939463168905523300304071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109252617558540697733738761 81939463168905523300304071)
      ·
        refine ⟨122909194753358284950456107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81939463168905523300304071 122909194753358284950456107)
        ·
          refine ⟨184363792130037427425684161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122909194753358284950456107 184363792130037427425684161)
          ·
            refine ⟨138272844097528070569263121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184363792130037427425684161 138272844097528070569263121)
            ·
              refine ⟨103704633073146052926947341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138272844097528070569263121 103704633073146052926947341)
              ·
                refine ⟨38889237402429769847605253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103704633073146052926947341 38889237402429769847605253)
                ·
                  refine ⟨7291732012955581846425985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38889237402429769847605253 7291732012955581846425985)
                  ·
                    refine ⟨5468799009716686384819489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291732012955581846425985 5468799009716686384819489)
                    ·
                      refine ⟨4101599257287514788614617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468799009716686384819489 4101599257287514788614617)
                      ·
                        rfl

theorem cell23_7987836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_7987836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987836 prefixEnd_7987836 := by exact prefixLift 7987836
  have htrace : WordTrace (prefixWord ++ tailWord_7987836) baseStart_7987836 baseEnd_7987836 := by
    simpa [prefixWord, tailWord_7987836, baseEnd_7987836] using wordTrace_append hprefix tailTrace_7987836
  have hstable : (prefixWord ++ tailWord_7987836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987836).length < 2 ^ (prefixWord ++ tailWord_7987836).sum := by decide
  have hdescent : baseEnd_7987836 < baseStart_7987836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987876 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 5]
def baseStart_7987876 : Nat := 118140960795 + 7987876 * 2 ^ 59
def prefixEnd_7987876 : Nat := 4983230072969 + 3 ^ 40 * 7987876 * 2
def baseEnd_7987876 : Nat := 455735532945966070234937

theorem tailTrace_7987876 : CollatzResearch.WordTrace tailWord_7987876 prefixEnd_7987876 455735532945966070234937 := by
  unfold tailWord_7987876
  simp only [CollatzResearch.WordTrace]
  refine ⟨145670886204648473727379741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194227848272864631636506321 145670886204648473727379741)
  ·
    refine ⟨54626582326743177647767403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145670886204648473727379741 54626582326743177647767403)
    ·
      refine ⟨81939873490114766471651105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54626582326743177647767403 81939873490114766471651105)
      ·
        refine ⟨61454905117586074853738329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81939873490114766471651105 61454905117586074853738329)
        ·
          refine ⟨46091178838189556140303747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61454905117586074853738329 46091178838189556140303747)
          ·
            refine ⟨69136768257284334210455621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46091178838189556140303747 69136768257284334210455621)
            ·
              refine ⟨12963144048240812664460429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69136768257284334210455621 12963144048240812664460429)
              ·
                refine ⟨4861179018090304749172661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12963144048240812664460429 4861179018090304749172661)
                ·
                  refine ⟨455735532945966070234937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861179018090304749172661 455735532945966070234937)
                  ·
                    rfl

theorem cell23_7987876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_7987876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987876 prefixEnd_7987876 := by exact prefixLift 7987876
  have htrace : WordTrace (prefixWord ++ tailWord_7987876) baseStart_7987876 baseEnd_7987876 := by
    simpa [prefixWord, tailWord_7987876, baseEnd_7987876] using wordTrace_append hprefix tailTrace_7987876
  have hstable : (prefixWord ++ tailWord_7987876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987876).length < 2 ^ (prefixWord ++ tailWord_7987876).sum := by decide
  have hdescent : baseEnd_7987876 < baseStart_7987876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987929 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_7987929 : Nat := 118140960795 + 7987929 * 2 ^ 59
def prefixEnd_7987929 : Nat := 4983230072969 + 3 ^ 40 * 7987929 * 2
def baseEnd_7987929 : Nat := 4101647010988382924751689

theorem tailTrace_7987929 : CollatzResearch.WordTrace tailWord_7987929 prefixEnd_7987929 4101647010988382924751689 := by
  unfold tailWord_7987929
  simp only [CollatzResearch.WordTrace]
  refine ⟨291343705478104937506438841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194229136985403291670959227 291343705478104937506438841)
  ·
    refine ⟨218507779108578703129829131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291343705478104937506438841 218507779108578703129829131)
    ·
      refine ⟨327761668662868054694743697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218507779108578703129829131 327761668662868054694743697)
      ·
        refine ⟨245821251497151041021057773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327761668662868054694743697 245821251497151041021057773)
        ·
          refine ⟨92182969311431640382896665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245821251497151041021057773 92182969311431640382896665)
          ·
            refine ⟨69137226983573730287172499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92182969311431640382896665 69137226983573730287172499)
            ·
              refine ⟨103705840475360595430758749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69137226983573730287172499 103705840475360595430758749)
              ·
                refine ⟨38889690178260223286534531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103705840475360595430758749 38889690178260223286534531)
                ·
                  refine ⟨58334535267390334929801797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38889690178260223286534531 58334535267390334929801797)
                  ·
                    refine ⟨10937725362635687799337837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58334535267390334929801797 10937725362635687799337837)
                    ·
                      refine ⟨4101647010988382924751689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937725362635687799337837 4101647010988382924751689)
                      ·
                        rfl

theorem cell23_7987929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_7987929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987929 prefixEnd_7987929 := by exact prefixLift 7987929
  have htrace : WordTrace (prefixWord ++ tailWord_7987929) baseStart_7987929 baseEnd_7987929 := by
    simpa [prefixWord, tailWord_7987929, baseEnd_7987929] using wordTrace_append hprefix tailTrace_7987929
  have hstable : (prefixWord ++ tailWord_7987929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987929).length < 2 ^ (prefixWord ++ tailWord_7987929).sum := by decide
  have hdescent : baseEnd_7987929 < baseStart_7987929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7987949 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 8]
def baseStart_7987949 : Nat := 118140960795 + 7987949 * 2 ^ 59
def prefixEnd_7987949 : Nat := 4983230072969 + 3 ^ 40 * 7987949 * 2
def baseEnd_7987949 : Nat := 455739697844608094055733

theorem tailTrace_7987949 : CollatzResearch.WordTrace tailWord_7987949 prefixEnd_7987949 455739697844608094055733 := by
  unfold tailWord_7987949
  simp only [CollatzResearch.WordTrace]
  refine ⟨291344434938032480922166901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194229623292021653948111267 291344434938032480922166901)
  ·
    refine ⟨27313540775440545086453147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291344434938032480922166901 27313540775440545086453147)
    ·
      refine ⟨40970311163160817629679721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27313540775440545086453147 40970311163160817629679721)
      ·
        refine ⟨30727733372370613222259791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40970311163160817629679721 30727733372370613222259791)
        ·
          refine ⟨46091600058555919833389687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30727733372370613222259791 46091600058555919833389687)
          ·
            refine ⟨69137400087833879750084531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46091600058555919833389687 69137400087833879750084531)
            ·
              refine ⟨103706100131750819625126797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69137400087833879750084531 103706100131750819625126797)
              ·
                refine ⟨38889787549406557359422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103706100131750819625126797 38889787549406557359422549)
                ·
                  refine ⟨455739697844608094055733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38889787549406557359422549 455739697844608094055733)
                  ·
                    rfl

theorem cell23_7987949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_7987949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7987949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7987949 prefixEnd_7987949 := by exact prefixLift 7987949
  have htrace : WordTrace (prefixWord ++ tailWord_7987949) baseStart_7987949 baseEnd_7987949 := by
    simpa [prefixWord, tailWord_7987949, baseEnd_7987949] using wordTrace_append hprefix tailTrace_7987949
  have hstable : (prefixWord ++ tailWord_7987949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7987949).length < 2 ^ (prefixWord ++ tailWord_7987949).sum := by decide
  have hdescent : baseEnd_7987949 < baseStart_7987949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7987949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988004 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_7988004 : Nat := 118140960795 + 7988004 * 2 ^ 59
def prefixEnd_7988004 : Nat := 4983230072969 + 3 ^ 40 * 7988004 * 2
def baseEnd_7988004 : Nat := 1367228507345823377104615

theorem tailTrace_7988004 : CollatzResearch.WordTrace tailWord_7988004 prefixEnd_7988004 1367228507345823377104615 := by
  unfold tailWord_7988004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145673220476416612657709533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194230960635222150210279377 145673220476416612657709533)
  ·
    refine ⟨54627457678656229746641075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145673220476416612657709533 54627457678656229746641075)
    ·
      refine ⟨81941186517984344619961613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54627457678656229746641075 81941186517984344619961613)
      ·
        refine ⟨30727944944244129232485605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81941186517984344619961613 30727944944244129232485605)
        ·
          refine ⟨5761489677045774231091051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30727944944244129232485605 5761489677045774231091051)
          ·
            refine ⟨8642234515568661346636577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761489677045774231091051 8642234515568661346636577)
            ·
              refine ⟨6481675886676496009977433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642234515568661346636577 6481675886676496009977433)
              ·
                refine ⟨4861256915007372007483075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481675886676496009977433 4861256915007372007483075)
                ·
                  refine ⟨7291885372511058011224613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861256915007372007483075 7291885372511058011224613)
                  ·
                    refine ⟨1367228507345823377104615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291885372511058011224613 1367228507345823377104615)
                    ·
                      rfl

theorem cell23_7988004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_7988004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988004 prefixEnd_7988004 := by exact prefixLift 7988004
  have htrace : WordTrace (prefixWord ++ tailWord_7988004) baseStart_7988004 baseEnd_7988004 := by
    simpa [prefixWord, tailWord_7988004, baseEnd_7988004] using wordTrace_append hprefix tailTrace_7988004
  have hstable : (prefixWord ++ tailWord_7988004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988004).length < 2 ^ (prefixWord ++ tailWord_7988004).sum := by decide
  have hdescent : baseEnd_7988004 < baseStart_7988004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988053 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7988053 : Nat := 118140960795 + 7988053 * 2 ^ 59
def prefixEnd_7988053 : Nat := 4983230072969 + 3 ^ 40 * 7988053 * 2
def baseEnd_7988053 : Nat := 4101710682589540439601119

theorem tailTrace_7988053 : CollatzResearch.WordTrace tailWord_7988053 prefixEnd_7988053 4101710682589540439601119 := by
  unfold tailWord_7988053
  simp only [CollatzResearch.WordTrace]
  refine ⟨291348228129655706683952813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194232152086437137789301875 291348228129655706683952813)
  ·
    refine ⟨109255585548620890006482305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291348228129655706683952813 109255585548620890006482305)
    ·
      refine ⟨81941689161465667504861729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109255585548620890006482305 81941689161465667504861729)
      ·
        refine ⟨61456266871099250628646297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81941689161465667504861729 61456266871099250628646297)
        ·
          refine ⟨46092200153324437971484723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61456266871099250628646297 46092200153324437971484723)
          ·
            refine ⟨69138300229986656957227085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46092200153324437971484723 69138300229986656957227085)
            ·
              refine ⟨25926862586244996358960157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69138300229986656957227085 25926862586244996358960157)
              ·
                refine ⟨9722573469841873634610059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25926862586244996358960157 9722573469841873634610059)
                ·
                  refine ⟨14583860204762810451915089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722573469841873634610059 14583860204762810451915089)
                  ·
                    refine ⟨10937895153572107838936317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14583860204762810451915089 10937895153572107838936317)
                    ·
                      refine ⟨4101710682589540439601119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937895153572107838936317 4101710682589540439601119)
                      ·
                        rfl

theorem cell23_7988053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7988053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988053 prefixEnd_7988053 := by exact prefixLift 7988053
  have htrace : WordTrace (prefixWord ++ tailWord_7988053) baseStart_7988053 baseEnd_7988053 := by
    simpa [prefixWord, tailWord_7988053, baseEnd_7988053] using wordTrace_append hprefix tailTrace_7988053
  have hstable : (prefixWord ++ tailWord_7988053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988053).length < 2 ^ (prefixWord ++ tailWord_7988053).sum := by decide
  have hdescent : baseEnd_7988053 < baseStart_7988053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988060 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7988060 : Nat := 118140960795 + 7988060 * 2 ^ 59
def prefixEnd_7988060 : Nat := 4983230072969 + 3 ^ 40 * 7988060 * 2
def baseEnd_7988060 : Nat := 1367238092318040637404529

theorem tailTrace_7988060 : CollatzResearch.WordTrace tailWord_7988060 prefixEnd_7988060 1367238092318040637404529 := by
  unfold tailWord_7988060
  simp only [CollatzResearch.WordTrace]
  refine ⟨145674241720315173439728817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194232322293753564586305089 145674241720315173439728817)
  ·
    refine ⟨109255681290236380079796613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145674241720315173439728817 109255681290236380079796613)
    ·
      refine ⟨20485440241919321264961865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109255681290236380079796613 20485440241919321264961865)
      ·
        refine ⟨15364080181439490948721399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20485440241919321264961865 15364080181439490948721399)
        ·
          refine ⟨23046120272159236423082099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364080181439490948721399 23046120272159236423082099)
          ·
            refine ⟨34569180408238854634623149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23046120272159236423082099 34569180408238854634623149)
            ·
              refine ⟨12963442653089570487983681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34569180408238854634623149 12963442653089570487983681)
              ·
                refine ⟨9722581989817177865987761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963442653089570487983681 9722581989817177865987761)
                ·
                  refine ⟨7291936492362883399490821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722581989817177865987761 7291936492362883399490821)
                  ·
                    refine ⟨1367238092318040637404529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7291936492362883399490821 1367238092318040637404529)
                    ·
                      rfl

theorem cell23_7988060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7988060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988060 prefixEnd_7988060 := by exact prefixLift 7988060
  have htrace : WordTrace (prefixWord ++ tailWord_7988060) baseStart_7988060 baseEnd_7988060 := by
    simpa [prefixWord, tailWord_7988060, baseEnd_7988060] using wordTrace_append hprefix tailTrace_7988060
  have hstable : (prefixWord ++ tailWord_7988060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988060).length < 2 ^ (prefixWord ++ tailWord_7988060).sum := by decide
  have hdescent : baseEnd_7988060 < baseStart_7988060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988067 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7988067 : Nat := 118140960795 + 7988067 * 2 ^ 59
def prefixEnd_7988067 : Nat := 4983230072969 + 3 ^ 40 * 7988067 * 2
def baseEnd_7988067 : Nat := 4101717871318703384826055

theorem tailTrace_7988067 : CollatzResearch.WordTrace tailWord_7988067 prefixEnd_7988067 4101717871318703384826055 := by
  unfold tailWord_7988067
  simp only [CollatzResearch.WordTrace]
  refine ⟨291348738751604987074962455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194232492501069991383308303 291348738751604987074962455)
  ·
    refine ⟨437023108127407480612443683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291348738751604987074962455 437023108127407480612443683)
    ·
      refine ⟨655534662191111220918665525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437023108127407480612443683 655534662191111220918665525)
      ·
        refine ⟨61456374580416676961124893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 655534662191111220918665525 61456374580416676961124893)
        ·
          refine ⟨23046140467656253860421835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61456374580416676961124893 23046140467656253860421835)
          ·
            refine ⟨34569210701484380790632753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23046140467656253860421835 34569210701484380790632753)
            ·
              refine ⟨25926908026113285592974565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34569210701484380790632753 25926908026113285592974565)
              ·
                refine ⟨4861295254896241048682731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25926908026113285592974565 4861295254896241048682731)
                ·
                  refine ⟨7291942882344361573024097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861295254896241048682731 7291942882344361573024097)
                  ·
                    refine ⟨5468957161758271179768073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291942882344361573024097 5468957161758271179768073)
                    ·
                      refine ⟨4101717871318703384826055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468957161758271179768073 4101717871318703384826055)
                      ·
                        rfl

theorem cell23_7988067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7988067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988067 prefixEnd_7988067 := by exact prefixLift 7988067
  have htrace : WordTrace (prefixWord ++ tailWord_7988067) baseStart_7988067 baseEnd_7988067 := by
    simpa [prefixWord, tailWord_7988067, baseEnd_7988067] using wordTrace_append hprefix tailTrace_7988067
  have hstable : (prefixWord ++ tailWord_7988067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988067).length < 2 ^ (prefixWord ++ tailWord_7988067).sum := by decide
  have hdescent : baseEnd_7988067 < baseStart_7988067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988069 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_7988069 : Nat := 118140960795 + 7988069 * 2 ^ 59
def prefixEnd_7988069 : Nat := 4983230072969 + 3 ^ 40 * 7988069 * 2
def baseEnd_7988069 : Nat := 1367239632760004125667015

theorem tailTrace_7988069 : CollatzResearch.WordTrace tailWord_7988069 prefixEnd_7988069 1367239632760004125667015 := by
  unfold tailWord_7988069
  simp only [CollatzResearch.WordTrace]
  refine ⟨291348811697597741416535261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194232541131731827611023507 291348811697597741416535261)
  ·
    refine ⟨109255804386599153031200723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291348811697597741416535261 109255804386599153031200723)
    ·
      refine ⟨163883706579898729546801085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109255804386599153031200723 163883706579898729546801085)
      ·
        refine ⟨61456389967462023580050407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163883706579898729546801085 61456389967462023580050407)
        ·
          refine ⟨92184584951193035370075611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61456389967462023580050407 92184584951193035370075611)
          ·
            refine ⟨138276877426789553055113417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92184584951193035370075611 138276877426789553055113417)
            ·
              refine ⟨103707658070092164791335063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138276877426789553055113417 103707658070092164791335063)
              ·
                refine ⟨155561487105138247187002595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103707658070092164791335063 155561487105138247187002595)
                ·
                  refine ⟨233342230657707370780503893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155561487105138247187002595 233342230657707370780503893)
                  ·
                    refine ⟨1367239632760004125667015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 233342230657707370780503893 1367239632760004125667015)
                    ·
                      rfl

theorem cell23_7988069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_7988069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988069 prefixEnd_7988069 := by exact prefixLift 7988069
  have htrace : WordTrace (prefixWord ++ tailWord_7988069) baseStart_7988069 baseEnd_7988069 := by
    simpa [prefixWord, tailWord_7988069, baseEnd_7988069] using wordTrace_append hprefix tailTrace_7988069
  have hstable : (prefixWord ++ tailWord_7988069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988069).length < 2 ^ (prefixWord ++ tailWord_7988069).sum := by decide
  have hdescent : baseEnd_7988069 < baseStart_7988069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988079 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_7988079 : Nat := 118140960795 + 7988079 * 2 ^ 59
def prefixEnd_7988079 : Nat := 4983230072969 + 3 ^ 40 * 7988079 * 2
def baseEnd_7988079 : Nat := 4101724033086557337875999

theorem tailTrace_7988079 : CollatzResearch.WordTrace tailWord_7988079 prefixEnd_7988079 4101724033086557337875999 := by
  unfold tailWord_7988079
  simp only [CollatzResearch.WordTrace]
  refine ⟨291349176427561513124399291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194232784285041008749599527 291349176427561513124399291)
  ·
    refine ⟨437023764641342269686598937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291349176427561513124399291 437023764641342269686598937)
    ·
      refine ⟨327767823481006702264949203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437023764641342269686598937 327767823481006702264949203)
      ·
        refine ⟨491651735221510053397423805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327767823481006702264949203 491651735221510053397423805)
        ·
          refine ⟨184369400708066270024033927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491651735221510053397423805 184369400708066270024033927)
          ·
            refine ⟨276554101062099405036050891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184369400708066270024033927 276554101062099405036050891)
            ·
              refine ⟨414831151593149107554076337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276554101062099405036050891 414831151593149107554076337)
              ·
                refine ⟨311123363694861830665557253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414831151593149107554076337 311123363694861830665557253)
                ·
                  refine ⟨58335630692786593249791985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311123363694861830665557253 58335630692786593249791985)
                  ·
                    refine ⟨43751723019589944937343989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58335630692786593249791985 43751723019589944937343989)
                    ·
                      refine ⟨4101724033086557337875999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43751723019589944937343989 4101724033086557337875999)
                      ·
                        rfl

theorem cell23_7988079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_7988079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988079 prefixEnd_7988079 := by exact prefixLift 7988079
  have htrace : WordTrace (prefixWord ++ tailWord_7988079) baseStart_7988079 baseEnd_7988079 := by
    simpa [prefixWord, tailWord_7988079, baseEnd_7988079] using wordTrace_append hprefix tailTrace_7988079
  have hstable : (prefixWord ++ tailWord_7988079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988079).length < 2 ^ (prefixWord ++ tailWord_7988079).sum := by decide
  have hdescent : baseEnd_7988079 < baseStart_7988079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988083 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 3]
def baseStart_7988083 : Nat := 118140960795 + 7988083 * 2 ^ 59
def prefixEnd_7988083 : Nat := 4983230072969 + 3 ^ 40 * 7988083 * 2
def baseEnd_7988083 : Nat := 4101726087009175322225981

theorem tailTrace_7988083 : CollatzResearch.WordTrace tailWord_7988083 prefixEnd_7988083 4101726087009175322225981 := by
  unfold tailWord_7988083
  simp only [CollatzResearch.WordTrace]
  refine ⟨291349322319547021807544903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194232881546364681205029935 291349322319547021807544903)
  ·
    refine ⟨437023983479320532711317355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291349322319547021807544903 437023983479320532711317355)
    ·
      refine ⟨655535975218980799066976033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437023983479320532711317355 655535975218980799066976033)
      ·
        refine ⟨491651981414235599300232025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655535975218980799066976033 491651981414235599300232025)
        ·
          refine ⟨368738986060676699475174019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491651981414235599300232025 368738986060676699475174019)
          ·
            refine ⟨553108479091015049212761029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368738986060676699475174019 553108479091015049212761029)
            ·
              refine ⟨103707839829565321727392693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 553108479091015049212761029 103707839829565321727392693)
              ·
                refine ⟨9722609984021748911943065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103707839829565321727392693 9722609984021748911943065)
                ·
                  refine ⟨7291957488016311683957299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722609984021748911943065 7291957488016311683957299)
                  ·
                    refine ⟨10937936232024467525935949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291957488016311683957299 10937936232024467525935949)
                    ·
                      refine ⟨4101726087009175322225981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10937936232024467525935949 4101726087009175322225981)
                      ·
                        rfl

theorem cell23_7988083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_7988083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988083 prefixEnd_7988083 := by exact prefixLift 7988083
  have htrace : WordTrace (prefixWord ++ tailWord_7988083) baseStart_7988083 baseEnd_7988083 := by
    simpa [prefixWord, tailWord_7988083, baseEnd_7988083] using wordTrace_append hprefix tailTrace_7988083
  have hstable : (prefixWord ++ tailWord_7988083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988083).length < 2 ^ (prefixWord ++ tailWord_7988083).sum := by decide
  have hdescent : baseEnd_7988083 < baseStart_7988083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988093 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_7988093 : Nat := 118140960795 + 7988093 * 2 ^ 59
def prefixEnd_7988093 : Nat := 4983230072969 + 3 ^ 40 * 7988093 * 2
def baseEnd_7988093 : Nat := 4101731221815720283100935

theorem tailTrace_7988093 : CollatzResearch.WordTrace tailWord_7988093 prefixEnd_7988093 4101731221815720283100935 := by
  unfold tailWord_7988093
  simp only [CollatzResearch.WordTrace]
  refine ⟨291349687049510793515408933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194233124699673862343605955 291349687049510793515408933)
  ·
    refine ⟨54628066321783273784139175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291349687049510793515408933 54628066321783273784139175)
    ·
      refine ⟨81942099482674910676208763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54628066321783273784139175 81942099482674910676208763)
      ·
        refine ⟨122913149224012366014313145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81942099482674910676208763 122913149224012366014313145)
        ·
          refine ⟨92184861918009274510734859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122913149224012366014313145 92184861918009274510734859)
          ·
            refine ⟨138277292877013911766102289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92184861918009274510734859 138277292877013911766102289)
            ·
              refine ⟨103707969657760433824576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138277292877013911766102289 103707969657760433824576717)
              ·
                refine ⟨38890488621660162684216269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103707969657760433824576717 38890488621660162684216269)
                ·
                  refine ⟨14583933233122561006581101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38890488621660162684216269 14583933233122561006581101)
                  ·
                    refine ⟨5468974962420960377467913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14583933233122561006581101 5468974962420960377467913)
                    ·
                      refine ⟨4101731221815720283100935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5468974962420960377467913 4101731221815720283100935)
                      ·
                        rfl

theorem cell23_7988093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_7988093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988093 prefixEnd_7988093 := by exact prefixLift 7988093
  have htrace : WordTrace (prefixWord ++ tailWord_7988093) baseStart_7988093 baseEnd_7988093 := by
    simpa [prefixWord, tailWord_7988093, baseEnd_7988093] using wordTrace_append hprefix tailTrace_7988093
  have hstable : (prefixWord ++ tailWord_7988093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988093).length < 2 ^ (prefixWord ++ tailWord_7988093).sum := by decide
  have hdescent : baseEnd_7988093 < baseStart_7988093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_7988139 : Nat := 118140960795 + 7988139 * 2 ^ 59
def prefixEnd_7988139 : Nat := 4983230072969 + 3 ^ 40 * 7988139 * 2
def baseEnd_7988139 : Nat := 4101754841925827103125723

theorem tailTrace_7988139 : CollatzResearch.WordTrace tailWord_7988139 prefixEnd_7988139 4101754841925827103125723 := by
  unfold tailWord_7988139
  simp only [CollatzResearch.WordTrace]
  refine ⟨291351364807344143371583471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194234243204896095581055647 291351364807344143371583471)
  ·
    refine ⟨437027047211016215057375207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291351364807344143371583471 437027047211016215057375207)
    ·
      refine ⟨655540570816524322586062811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437027047211016215057375207 655540570816524322586062811)
      ·
        refine ⟨983310856224786483879094217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655540570816524322586062811 983310856224786483879094217)
        ·
          refine ⟨737483142168589862909320663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983310856224786483879094217 737483142168589862909320663)
          ·
            refine ⟨1106224713252884794363980995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737483142168589862909320663 1106224713252884794363980995)
            ·
              refine ⟨1659337069879327191545971493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106224713252884794363980995 1659337069879327191545971493)
              ·
                refine ⟨311125700602373848414869655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1659337069879327191545971493 311125700602373848414869655)
                ·
                  refine ⟨466688550903560772622304483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311125700602373848414869655 466688550903560772622304483)
                  ·
                    refine ⟨700032826355341158933456725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 466688550903560772622304483 700032826355341158933456725)
                    ·
                      refine ⟨4101754841925827103125723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 700032826355341158933456725 4101754841925827103125723)
                      ·
                        rfl

theorem cell23_7988139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_7988139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988139 prefixEnd_7988139 := by exact prefixLift 7988139
  have htrace : WordTrace (prefixWord ++ tailWord_7988139) baseStart_7988139 baseEnd_7988139 := by
    simpa [prefixWord, tailWord_7988139, baseEnd_7988139] using wordTrace_append hprefix tailTrace_7988139
  have hstable : (prefixWord ++ tailWord_7988139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988139).length < 2 ^ (prefixWord ++ tailWord_7988139).sum := by decide
  have hdescent : baseEnd_7988139 < baseStart_7988139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988140 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_7988140 : Nat := 118140960795 + 7988140 * 2 ^ 59
def prefixEnd_7988140 : Nat := 4983230072969 + 3 ^ 40 * 7988140 * 2
def baseEnd_7988140 : Nat := 4101755355406481599213219

theorem tailTrace_7988140 : CollatzResearch.WordTrace tailWord_7988140 prefixEnd_7988140 4101755355406481599213219 := by
  unfold tailWord_7988140
  simp only [CollatzResearch.WordTrace]
  refine ⟨145675700640170260271184937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194234267520227013694913249 145675700640170260271184937)
  ·
    refine ⟨109256775480127695203388703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145675700640170260271184937 109256775480127695203388703)
    ·
      refine ⟨163885163220191542805083055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109256775480127695203388703 163885163220191542805083055)
      ·
        refine ⟨245827744830287314207624583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163885163220191542805083055 245827744830287314207624583)
        ·
          refine ⟨368741617245430971311436875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245827744830287314207624583 368741617245430971311436875)
          ·
            refine ⟨553112425868146456967155313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368741617245430971311436875 553112425868146456967155313)
            ·
              refine ⟨414834319401109842725366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553112425868146456967155313 414834319401109842725366485)
              ·
                refine ⟨9722679360963511938875777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414834319401109842725366485 9722679360963511938875777)
                ·
                  refine ⟨7292009520722633954156833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722679360963511938875777 7292009520722633954156833)
                  ·
                    refine ⟨5469007140541975465617625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7292009520722633954156833 5469007140541975465617625)
                    ·
                      refine ⟨4101755355406481599213219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469007140541975465617625 4101755355406481599213219)
                      ·
                        rfl

theorem cell23_7988140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_7988140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988140 prefixEnd_7988140 := by exact prefixLift 7988140
  have htrace : WordTrace (prefixWord ++ tailWord_7988140) baseStart_7988140 baseEnd_7988140 := by
    simpa [prefixWord, tailWord_7988140, baseEnd_7988140] using wordTrace_append hprefix tailTrace_7988140
  have hstable : (prefixWord ++ tailWord_7988140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988140).length < 2 ^ (prefixWord ++ tailWord_7988140).sum := by decide
  have hdescent : baseEnd_7988140 < baseStart_7988140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988180 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 5]
def baseStart_7988180 : Nat := 118140960795 + 7988180 * 2 ^ 59
def prefixEnd_7988180 : Nat := 4983230072969 + 3 ^ 40 * 7988180 * 2
def baseEnd_7988180 : Nat := 455752877181406826968115

theorem tailTrace_7988180 : CollatzResearch.WordTrace tailWord_7988180 prefixEnd_7988180 455752877181406826968115 := by
  unfold tailWord_7988180
  simp only [CollatzResearch.WordTrace]
  refine ⟨145676430100097803686912997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194235240133463738249217329 145676430100097803686912997)
  ·
    refine ⟨27314330643768338191296187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145676430100097803686912997 27314330643768338191296187)
    ·
      refine ⟨40971495965652507286944281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27314330643768338191296187 40971495965652507286944281)
      ·
        refine ⟨30728621974239380465208211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40971495965652507286944281 30728621974239380465208211)
        ·
          refine ⟨46092932961359070697812317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30728621974239380465208211 46092932961359070697812317)
          ·
            refine ⟨17284849860509651511679619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46092932961359070697812317 17284849860509651511679619)
            ·
              refine ⟨25927274790764477267519429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17284849860509651511679619 25927274790764477267519429)
              ·
                refine ⟨4861364023268339487659893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25927274790764477267519429 4861364023268339487659893)
                ·
                  refine ⟨455752877181406826968115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861364023268339487659893 455752877181406826968115)
                  ·
                    rfl

theorem cell23_7988180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_7988180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988180 prefixEnd_7988180 := by exact prefixLift 7988180
  have htrace : WordTrace (prefixWord ++ tailWord_7988180) baseStart_7988180 baseEnd_7988180 := by
    simpa [prefixWord, tailWord_7988180, baseEnd_7988180] using wordTrace_append hprefix tailTrace_7988180
  have hstable : (prefixWord ++ tailWord_7988180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988180).length < 2 ^ (prefixWord ++ tailWord_7988180).sum := by decide
  have hdescent : baseEnd_7988180 < baseStart_7988180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988210 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_7988210 : Nat := 118140960795 + 7988210 * 2 ^ 59
def prefixEnd_7988210 : Nat := 4983230072969 + 3 ^ 40 * 7988210 * 2
def baseEnd_7988210 : Nat := 1367263766350765441779299

theorem tailTrace_7988210 : CollatzResearch.WordTrace tailWord_7988210 prefixEnd_7988210 1367263766350765441779299 := by
  unfold tailWord_7988210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72838488597521730624354521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194235969593391281664945389 72838488597521730624354521)
  ·
    refine ⟨54628866448141297968265891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72838488597521730624354521 54628866448141297968265891)
    ·
      refine ⟨81943299672211946952398837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54628866448141297968265891 81943299672211946952398837)
      ·
        refine ⟨7682184344269870026787391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81943299672211946952398837 7682184344269870026787391)
        ·
          refine ⟨11523276516404805040181087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682184344269870026787391 11523276516404805040181087)
          ·
            refine ⟨17284914774607207560271631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523276516404805040181087 17284914774607207560271631)
            ·
              refine ⟨25927372161910811340407447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17284914774607207560271631 25927372161910811340407447)
              ·
                refine ⟨38891058242866217010611171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25927372161910811340407447 38891058242866217010611171)
                ·
                  refine ⟨58336587364299325515916757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38891058242866217010611171 58336587364299325515916757)
                  ·
                    refine ⟨1367263766350765441779299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58336587364299325515916757 1367263766350765441779299)
                    ·
                      rfl

theorem cell23_7988210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_7988210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988210 prefixEnd_7988210 := by exact prefixLift 7988210
  have htrace : WordTrace (prefixWord ++ tailWord_7988210) baseStart_7988210 baseEnd_7988210 := by
    simpa [prefixWord, tailWord_7988210, baseEnd_7988210] using wordTrace_append hprefix tailTrace_7988210
  have hstable : (prefixWord ++ tailWord_7988210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988210).length < 2 ^ (prefixWord ++ tailWord_7988210).sum := by decide
  have hdescent : baseEnd_7988210 < baseStart_7988210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988212 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7988212 : Nat := 118140960795 + 7988212 * 2 ^ 59
def prefixEnd_7988212 : Nat := 4983230072969 + 3 ^ 40 * 7988212 * 2
def baseEnd_7988212 : Nat := 4101792326013605317512889

theorem tailTrace_7988212 : CollatzResearch.WordTrace tailWord_7988212 prefixEnd_7988212 4101792326013605317512889 := by
  unfold tailWord_7988212
  simp only [CollatzResearch.WordTrace]
  refine ⟨145677013668039838419495445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194236018224053117892660593 145677013668039838419495445)
  ·
    refine ⟨6828610015689367425913849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145677013668039838419495445 6828610015689367425913849)
    ·
      refine ⟨5121457511767025569435387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6828610015689367425913849 5121457511767025569435387)
      ·
        refine ⟨7682186267650538354153081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121457511767025569435387 7682186267650538354153081)
        ·
          refine ⟨5761639700737903765614811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682186267650538354153081 5761639700737903765614811)
          ·
            refine ⟨8642459551106855648422217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761639700737903765614811 8642459551106855648422217)
            ·
              refine ⟨6481844663330141736316663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642459551106855648422217 6481844663330141736316663)
              ·
                refine ⟨9722766994995212604474995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481844663330141736316663 9722766994995212604474995)
                ·
                  refine ⟨14584150492492818906712493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722766994995212604474995 14584150492492818906712493)
                  ·
                    refine ⟨5469056434684807090017185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14584150492492818906712493 5469056434684807090017185)
                    ·
                      refine ⟨4101792326013605317512889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469056434684807090017185 4101792326013605317512889)
                      ·
                        rfl

theorem cell23_7988212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7988212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988212 prefixEnd_7988212 := by exact prefixLift 7988212
  have htrace : WordTrace (prefixWord ++ tailWord_7988212) baseStart_7988212 baseEnd_7988212 := by
    simpa [prefixWord, tailWord_7988212, baseEnd_7988212] using wordTrace_append hprefix tailTrace_7988212
  have hstable : (prefixWord ++ tailWord_7988212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988212).length < 2 ^ (prefixWord ++ tailWord_7988212).sum := by decide
  have hdescent : baseEnd_7988212 < baseStart_7988212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988233 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_7988233 : Nat := 118140960795 + 7988233 * 2 ^ 59
def prefixEnd_7988233 : Nat := 4983230072969 + 3 ^ 40 * 7988233 * 2
def baseEnd_7988233 : Nat := 4101803109107349735350291

theorem tailTrace_7988233 : CollatzResearch.WordTrace tailWord_7988233 prefixEnd_7988233 4101803109107349735350291 := by
  unfold tailWord_7988233
  simp only [CollatzResearch.WordTrace]
  refine ⟨291354793269003597425505353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194236528846002398283670235 291354793269003597425505353)
  ·
    refine ⟨218516094951752698069129015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291354793269003597425505353 218516094951752698069129015)
    ·
      refine ⟨327774142427629047103693523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218516094951752698069129015 327774142427629047103693523)
      ·
        refine ⟨491661213641443570655540285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327774142427629047103693523 491661213641443570655540285)
        ·
          refine ⟨184372955115541338995827607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491661213641443570655540285 184372955115541338995827607)
          ·
            refine ⟨276559432673312008493741411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184372955115541338995827607 276559432673312008493741411)
            ·
              refine ⟨414839149009968012740612117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276559432673312008493741411 414839149009968012740612117)
              ·
                refine ⟨19445585109842250597216193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414839149009968012740612117 19445585109842250597216193)
                ·
                  refine ⟨14584188832381687947912145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19445585109842250597216193 14584188832381687947912145)
                  ·
                    refine ⟨10938141624286265960934109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14584188832381687947912145 10938141624286265960934109)
                    ·
                      refine ⟨4101803109107349735350291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938141624286265960934109 4101803109107349735350291)
                      ·
                        rfl

theorem cell23_7988233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_7988233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988233 prefixEnd_7988233 := by exact prefixLift 7988233
  have htrace : WordTrace (prefixWord ++ tailWord_7988233) baseStart_7988233 baseEnd_7988233 := by
    simpa [prefixWord, tailWord_7988233, baseEnd_7988233] using wordTrace_append hprefix tailTrace_7988233
  have hstable : (prefixWord ++ tailWord_7988233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988233).length < 2 ^ (prefixWord ++ tailWord_7988233).sum := by decide
  have hdescent : baseEnd_7988233 < baseStart_7988233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988313 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_7988313 : Nat := 118140960795 + 7988313 * 2 ^ 59
def prefixEnd_7988313 : Nat := 4983230072969 + 3 ^ 40 * 7988313 * 2
def baseEnd_7988313 : Nat := 1367281395853236474116641

theorem tailTrace_7988313 : CollatzResearch.WordTrace tailWord_7988313 prefixEnd_7988313 1367281395853236474116641 := by
  unfold tailWord_7988313
  simp only [CollatzResearch.WordTrace]
  refine ⟨291357711108713771088417593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194238474072475847392278395 291357711108713771088417593)
  ·
    refine ⟨218518283331535328316313195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291357711108713771088417593 218518283331535328316313195)
    ·
      refine ⟨327777424997302992474469793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218518283331535328316313195 327777424997302992474469793)
      ·
        refine ⟨245833068747977244355852345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327777424997302992474469793 245833068747977244355852345)
        ·
          refine ⟨184374801560982933266889259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245833068747977244355852345 184374801560982933266889259)
          ·
            refine ⟨276562202341474399900333889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184374801560982933266889259 276562202341474399900333889)
            ·
              refine ⟨207421651756105799925250417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276562202341474399900333889 207421651756105799925250417)
              ·
                refine ⟨155566238817079349943937813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207421651756105799925250417 155566238817079349943937813)
                ·
                  refine ⟨7292167444550594528622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155566238817079349943937813 7292167444550594528622085)
                  ·
                    refine ⟨1367281395853236474116641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292167444550594528622085 1367281395853236474116641)
                    ·
                      rfl

theorem cell23_7988313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_7988313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988313 prefixEnd_7988313 := by exact prefixLift 7988313
  have htrace : WordTrace (prefixWord ++ tailWord_7988313) baseStart_7988313 baseEnd_7988313 := by
    simpa [prefixWord, tailWord_7988313, baseEnd_7988313] using wordTrace_append hprefix tailTrace_7988313
  have hstable : (prefixWord ++ tailWord_7988313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988313).length < 2 ^ (prefixWord ++ tailWord_7988313).sum := by decide
  have hdescent : baseEnd_7988313 < baseStart_7988313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988317 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7988317 : Nat := 118140960795 + 7988317 * 2 ^ 59
def prefixEnd_7988317 : Nat := 4983230072969 + 3 ^ 40 * 7988317 * 2
def baseEnd_7988317 : Nat := 1367282080494109135566635

theorem tailTrace_7988317 : CollatzResearch.WordTrace tailWord_7988317 prefixEnd_7988317 1367282080494109135566635 := by
  unfold tailWord_7988317
  simp only [CollatzResearch.WordTrace]
  refine ⟨291357857000699279771563205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194238571333799519847708803 291357857000699279771563205)
  ·
    refine ⟨54629598187631114957168101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291357857000699279771563205 54629598187631114957168101)
    ·
      refine ⟨10243049660180834054469019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54629598187631114957168101 10243049660180834054469019)
      ·
        refine ⟨15364574490271251081703529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243049660180834054469019 15364574490271251081703529)
        ·
          refine ⟨11523430867703438311277647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15364574490271251081703529 11523430867703438311277647)
          ·
            refine ⟨17285146301555157466916471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523430867703438311277647 17285146301555157466916471)
            ·
              refine ⟨25927719452332736200374707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17285146301555157466916471 25927719452332736200374707)
              ·
                refine ⟨38891579178499104300562061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25927719452332736200374707 38891579178499104300562061)
                ·
                  refine ⟨14584342191937164112710773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38891579178499104300562061 14584342191937164112710773)
                  ·
                    refine ⟨1367282080494109135566635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14584342191937164112710773 1367282080494109135566635)
                    ·
                      rfl

theorem cell23_7988317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7988317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988317 prefixEnd_7988317 := by exact prefixLift 7988317
  have htrace : WordTrace (prefixWord ++ tailWord_7988317) baseStart_7988317 baseEnd_7988317 := by
    simpa [prefixWord, tailWord_7988317, baseEnd_7988317] using wordTrace_append hprefix tailTrace_7988317
  have hstable : (prefixWord ++ tailWord_7988317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988317).length < 2 ^ (prefixWord ++ tailWord_7988317).sum := by decide
  have hdescent : baseEnd_7988317 < baseStart_7988317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988330 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7988330 : Nat := 118140960795 + 7988330 * 2 ^ 59
def prefixEnd_7988330 : Nat := 4983230072969 + 3 ^ 40 * 7988330 * 2
def baseEnd_7988330 : Nat := 1367284305576945285279115

theorem tailTrace_7988330 : CollatzResearch.WordTrace tailWord_7988330 prefixEnd_7988330 1367284305576945285279115 := by
  unfold tailWord_7988330
  simp only [CollatzResearch.WordTrace]
  refine ⟨72839582787413045747946611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194238887433101455327857629 72839582787413045747946611)
  ·
    refine ⟨109259374181119568621919917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72839582787413045747946611 109259374181119568621919917)
    ·
      refine ⟨40972265317919838233219969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109259374181119568621919917 40972265317919838233219969)
      ·
        refine ⟨30729198988439878674914977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40972265317919838233219969 30729198988439878674914977)
        ·
          refine ⟨23046899241329909006186233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30729198988439878674914977 23046899241329909006186233)
          ·
            refine ⟨17285174430997431754639675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23046899241329909006186233 17285174430997431754639675)
            ·
              refine ⟨25927761646496147631959513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17285174430997431754639675 25927761646496147631959513)
              ·
                refine ⟨19445821234872110723969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25927761646496147631959513 19445821234872110723969635)
                ·
                  refine ⟨29168731852308166085954453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19445821234872110723969635 29168731852308166085954453)
                  ·
                    refine ⟨1367284305576945285279115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29168731852308166085954453 1367284305576945285279115)
                    ·
                      rfl

theorem cell23_7988330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7988330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988330 prefixEnd_7988330 := by exact prefixLift 7988330
  have htrace : WordTrace (prefixWord ++ tailWord_7988330) baseStart_7988330 baseEnd_7988330 := by
    simpa [prefixWord, tailWord_7988330, baseEnd_7988330] using wordTrace_append hprefix tailTrace_7988330
  have hstable : (prefixWord ++ tailWord_7988330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988330).length < 2 ^ (prefixWord ++ tailWord_7988330).sum := by decide
  have hdescent : baseEnd_7988330 < baseStart_7988330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988391 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7988391 : Nat := 118140960795 + 7988391 * 2 ^ 59
def prefixEnd_7988391 : Nat := 4983230072969 + 3 ^ 40 * 7988391 * 2
def baseEnd_7988391 : Nat := 4101884239050760117174565

theorem tailTrace_7988391 : CollatzResearch.WordTrace tailWord_7988391 prefixEnd_7988391 4101884239050760117174565 := by
  unfold tailWord_7988391
  simp only [CollatzResearch.WordTrace]
  refine ⟨291360556002431190409757027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194240370668287460273171351 291360556002431190409757027)
  ·
    refine ⟨437040834003646785614635541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291360556002431190409757027 437040834003646785614635541)
    ·
      refine ⟨20486289093920943075686041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 437040834003646785614635541 20486289093920943075686041)
      ·
        refine ⟨15364716820440707306764531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20486289093920943075686041 15364716820440707306764531)
        ·
          refine ⟨23047075230661060960146797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364716820440707306764531 23047075230661060960146797)
          ·
            refine ⟨8642653211497897860055049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23047075230661060960146797 8642653211497897860055049)
            ·
              refine ⟨6481989908623423395041287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8642653211497897860055049 6481989908623423395041287)
              ·
                refine ⟨9722984862935135092561931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481989908623423395041287 9722984862935135092561931)
                ·
                  refine ⟨14584477294402702638842897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9722984862935135092561931 14584477294402702638842897)
                  ·
                    refine ⟨10938357970802026979132173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14584477294402702638842897 10938357970802026979132173)
                    ·
                      refine ⟨4101884239050760117174565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938357970802026979132173 4101884239050760117174565)
                      ·
                        rfl

theorem cell23_7988391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7988391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988391 prefixEnd_7988391 := by exact prefixLift 7988391
  have htrace : WordTrace (prefixWord ++ tailWord_7988391) baseStart_7988391 baseEnd_7988391 := by
    simpa [prefixWord, tailWord_7988391, baseEnd_7988391] using wordTrace_append hprefix tailTrace_7988391
  have hstable : (prefixWord ++ tailWord_7988391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988391).length < 2 ^ (prefixWord ++ tailWord_7988391).sum := by decide
  have hdescent : baseEnd_7988391 < baseStart_7988391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988403 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 6]
def baseStart_7988403 : Nat := 118140960795 + 7988403 * 2 ^ 59
def prefixEnd_7988403 : Nat := 4983230072969 + 3 ^ 40 * 7988403 * 2
def baseEnd_7988403 : Nat := 1367296800272871356741503

theorem tailTrace_7988403 : CollatzResearch.WordTrace tailWord_7988403 prefixEnd_7988403 1367296800272871356741503 := by
  unfold tailWord_7988403
  simp only [CollatzResearch.WordTrace]
  refine ⟨291360993678387716459193863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194240662452258477639462575 291360993678387716459193863)
  ·
    refine ⟨437041490517581574688790795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291360993678387716459193863 437041490517581574688790795)
    ·
      refine ⟨655562235776372362033186193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437041490517581574688790795 655562235776372362033186193)
      ·
        refine ⟨491671676832279271524889645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655562235776372362033186193 491671676832279271524889645)
        ·
          refine ⟨184376878812104726821833617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491671676832279271524889645 184376878812104726821833617)
          ·
            refine ⟨138282659109078545116375213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184376878812104726821833617 138282659109078545116375213)
            ·
              refine ⟨51855997165904454418640705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138282659109078545116375213 51855997165904454418640705)
              ·
                refine ⟨38891997874428340813980529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51855997165904454418640705 38891997874428340813980529)
                ·
                  refine ⟨29168998405821255610485397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38891997874428340813980529 29168998405821255610485397)
                  ·
                    refine ⟨1367296800272871356741503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29168998405821255610485397 1367296800272871356741503)
                    ·
                      rfl

theorem cell23_7988403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_7988403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988403 prefixEnd_7988403 := by exact prefixLift 7988403
  have htrace : WordTrace (prefixWord ++ tailWord_7988403) baseStart_7988403 baseEnd_7988403 := by
    simpa [prefixWord, tailWord_7988403, baseEnd_7988403] using wordTrace_append hprefix tailTrace_7988403
  have hstable : (prefixWord ++ tailWord_7988403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988403).length < 2 ^ (prefixWord ++ tailWord_7988403).sum := by decide
  have hdescent : baseEnd_7988403 < baseStart_7988403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988418 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7988418 : Nat := 118140960795 + 7988418 * 2 ^ 59
def prefixEnd_7988418 : Nat := 4983230072969 + 3 ^ 40 * 7988418 * 2
def baseEnd_7988418 : Nat := 4101898103028431511536941

theorem tailTrace_7988418 : CollatzResearch.WordTrace tailWord_7988418 prefixEnd_7988418 4101898103028431511536941 := by
  unfold tailWord_7988418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72840385193333343505247477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194241027182222249347326605 72840385193333343505247477)
  ·
    refine ⟨6828786111875000953616951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72840385193333343505247477 6828786111875000953616951)
    ·
      refine ⟨10243179167812501430425427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828786111875000953616951 10243179167812501430425427)
      ·
        refine ⟨15364768751718752145638141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243179167812501430425427 15364768751718752145638141)
        ·
          refine ⟨5761788281894532054614303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15364768751718752145638141 5761788281894532054614303)
          ·
            refine ⟨8642682422841798081921455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761788281894532054614303 8642682422841798081921455)
            ·
              refine ⟨12964023634262697122882183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642682422841798081921455 12964023634262697122882183)
              ·
                refine ⟨19446035451394045684323275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12964023634262697122882183 19446035451394045684323275)
                ·
                  refine ⟨29169053177091068526484913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19446035451394045684323275 29169053177091068526484913)
                  ·
                    refine ⟨21876789882818301394863685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29169053177091068526484913 21876789882818301394863685)
                    ·
                      refine ⟨4101898103028431511536941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21876789882818301394863685 4101898103028431511536941)
                      ·
                        rfl

theorem cell23_7988418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7988418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988418 prefixEnd_7988418 := by exact prefixLift 7988418
  have htrace : WordTrace (prefixWord ++ tailWord_7988418) baseStart_7988418 baseEnd_7988418 := by
    simpa [prefixWord, tailWord_7988418, baseEnd_7988418] using wordTrace_append hprefix tailTrace_7988418
  have hstable : (prefixWord ++ tailWord_7988418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988418).length < 2 ^ (prefixWord ++ tailWord_7988418).sum := by decide
  have hdescent : baseEnd_7988418 < baseStart_7988418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988478 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7988478 : Nat := 118140960795 + 7988478 * 2 ^ 59
def prefixEnd_7988478 : Nat := 4983230072969 + 3 ^ 40 * 7988478 * 2
def baseEnd_7988478 : Nat := 4101928911867701276786665

theorem tailTrace_7988478 : CollatzResearch.WordTrace tailWord_7988478 prefixEnd_7988478 4101928911867701276786665 := by
  unfold tailWord_7988478
  simp only [CollatzResearch.WordTrace]
  refine ⟨36420466144139500533521761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194242486102077336178782725 36420466144139500533521761)
  ·
    refine ⟨27315349608104625400141321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36420466144139500533521761 27315349608104625400141321)
    ·
      refine ⟨20486512206078469050105991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27315349608104625400141321 20486512206078469050105991)
      ·
        refine ⟨30729768309117703575158987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20486512206078469050105991 30729768309117703575158987)
        ·
          refine ⟨46094652463676555362738481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30729768309117703575158987 46094652463676555362738481)
          ·
            refine ⟨34570989347757416522053861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46094652463676555362738481 34570989347757416522053861)
            ·
              refine ⟨6482060502704515597885099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34570989347757416522053861 6482060502704515597885099)
              ·
                refine ⟨9723090754056773396827649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482060502704515597885099 9723090754056773396827649)
                ·
                  refine ⟨7292318065542580047620737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9723090754056773396827649 7292318065542580047620737)
                  ·
                    refine ⟨5469238549156935035715553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7292318065542580047620737 5469238549156935035715553)
                    ·
                      refine ⟨4101928911867701276786665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469238549156935035715553 4101928911867701276786665)
                      ·
                        rfl

theorem cell23_7988478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7988478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988478 prefixEnd_7988478 := by exact prefixLift 7988478
  have htrace : WordTrace (prefixWord ++ tailWord_7988478) baseStart_7988478 baseEnd_7988478 := by
    simpa [prefixWord, tailWord_7988478, baseEnd_7988478] using wordTrace_append hprefix tailTrace_7988478
  have hstable : (prefixWord ++ tailWord_7988478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988478).length < 2 ^ (prefixWord ++ tailWord_7988478).sum := by decide
  have hdescent : baseEnd_7988478 < baseStart_7988478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988517 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_7988517 : Nat := 118140960795 + 7988517 * 2 ^ 59
def prefixEnd_7988517 : Nat := 4983230072969 + 3 ^ 40 * 7988517 * 2
def baseEnd_7988517 : Nat := 4101948937613226624198985

theorem tailTrace_7988517 : CollatzResearch.WordTrace tailWord_7988517 prefixEnd_7988517 4101948937613226624198985 := by
  unfold tailWord_7988517
  simp only [CollatzResearch.WordTrace]
  refine ⟨291365151599974713928843805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194243434399983142619229203 291365151599974713928843805)
  ·
    refine ⟨109261931849990517723316427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291365151599974713928843805 109261931849990517723316427)
    ·
      refine ⟨163892897774985776584974641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109261931849990517723316427 163892897774985776584974641)
      ·
        refine ⟨122919673331239332438730981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163892897774985776584974641 122919673331239332438730981)
        ·
          refine ⟨23047438749607374832262059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122919673331239332438730981 23047438749607374832262059)
          ·
            refine ⟨34571158124411062248393089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047438749607374832262059 34571158124411062248393089)
            ·
              refine ⟨25928368593308296686294817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34571158124411062248393089 25928368593308296686294817)
              ·
                refine ⟨19446276444981222514721113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25928368593308296686294817 19446276444981222514721113)
                ·
                  refine ⟨14584707333735916886040835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19446276444981222514721113 14584707333735916886040835)
                  ·
                    refine ⟨21877061000603875329061253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14584707333735916886040835 21877061000603875329061253)
                    ·
                      refine ⟨4101948937613226624198985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21877061000603875329061253 4101948937613226624198985)
                      ·
                        rfl

theorem cell23_7988517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_7988517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988517 prefixEnd_7988517 := by exact prefixLift 7988517
  have htrace : WordTrace (prefixWord ++ tailWord_7988517) baseStart_7988517 baseEnd_7988517 := by
    simpa [prefixWord, tailWord_7988517, baseEnd_7988517] using wordTrace_append hprefix tailTrace_7988517
  have hstable : (prefixWord ++ tailWord_7988517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988517).length < 2 ^ (prefixWord ++ tailWord_7988517).sum := by decide
  have hdescent : baseEnd_7988517 < baseStart_7988517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988634 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_7988634 : Nat := 118140960795 + 7988634 * 2 ^ 59
def prefixEnd_7988634 : Nat := 4983230072969 + 3 ^ 40 * 7988634 * 2
def baseEnd_7988634 : Nat := 1367336338283267555478649

theorem tailTrace_7988634 : CollatzResearch.WordTrace tailWord_7988634 prefixEnd_7988634 1367336338283267555478649 := by
  unfold tailWord_7988634
  simp only [CollatzResearch.WordTrace]
  refine ⟨72842354735137710727713239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194246279293700561940568637 72842354735137710727713239)
  ·
    refine ⟨109263532102706566091569859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72842354735137710727713239 109263532102706566091569859)
    ·
      refine ⟨163895298154059849137354789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109263532102706566091569859 163895298154059849137354789)
      ·
        refine ⟨30730368403886221713254023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163895298154059849137354789 30730368403886221713254023)
        ·
          refine ⟨46095552605829332569881035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730368403886221713254023 46095552605829332569881035)
          ·
            refine ⟨69143328908743998854821553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46095552605829332569881035 69143328908743998854821553)
            ·
              refine ⟨51857496681557999141116165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69143328908743998854821553 51857496681557999141116165)
              ·
                refine ⟨9723280627792124838959281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51857496681557999141116165 9723280627792124838959281)
                ·
                  refine ⟨7292460470844093629219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9723280627792124838959281 7292460470844093629219461)
                  ·
                    refine ⟨1367336338283267555478649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292460470844093629219461 1367336338283267555478649)
                    ·
                      rfl

theorem cell23_7988634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_7988634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988634 prefixEnd_7988634 := by exact prefixLift 7988634
  have htrace : WordTrace (prefixWord ++ tailWord_7988634) baseStart_7988634 baseEnd_7988634 := by
    simpa [prefixWord, tailWord_7988634, baseEnd_7988634] using wordTrace_append hprefix tailTrace_7988634
  have hstable : (prefixWord ++ tailWord_7988634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988634).length < 2 ^ (prefixWord ++ tailWord_7988634).sum := by decide
  have hdescent : baseEnd_7988634 < baseStart_7988634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988637 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7988637 : Nat := 118140960795 + 7988637 * 2 ^ 59
def prefixEnd_7988637 : Nat := 4983230072969 + 3 ^ 40 * 7988637 * 2
def baseEnd_7988637 : Nat := 4102010555291766154698433

theorem tailTrace_7988637 : CollatzResearch.WordTrace tailWord_7988637 prefixEnd_7988637 4102010555291766154698433 := by
  unfold tailWord_7988637
  simp only [CollatzResearch.WordTrace]
  refine ⟨291369528359539974423212165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194246352239693316282141443 291369528359539974423212165)
  ·
    refine ⟨54631786567413745204352281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291369528359539974423212165 54631786567413745204352281)
    ·
      refine ⟨40973839925560308903264211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54631786567413745204352281 40973839925560308903264211)
      ·
        refine ⟨61460759888340463354896317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40973839925560308903264211 61460759888340463354896317)
        ·
          refine ⟨23047784958127673758086119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61460759888340463354896317 23047784958127673758086119)
          ·
            refine ⟨34571677437191510637129179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047784958127673758086119 34571677437191510637129179)
            ·
              refine ⟨51857516155787265955693769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571677437191510637129179 51857516155787265955693769)
              ·
                refine ⟨38893137116840449466770327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51857516155787265955693769 38893137116840449466770327)
                ·
                  refine ⟨58339705675260674200155491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38893137116840449466770327 58339705675260674200155491)
                  ·
                    refine ⟨87509558512891011300233237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58339705675260674200155491 87509558512891011300233237)
                    ·
                      refine ⟨4102010555291766154698433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87509558512891011300233237 4102010555291766154698433)
                      ·
                        rfl

theorem cell23_7988637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7988637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988637 prefixEnd_7988637 := by exact prefixLift 7988637
  have htrace : WordTrace (prefixWord ++ tailWord_7988637) baseStart_7988637 baseEnd_7988637 := by
    simpa [prefixWord, tailWord_7988637, baseEnd_7988637] using wordTrace_append hprefix tailTrace_7988637
  have hstable : (prefixWord ++ tailWord_7988637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988637).length < 2 ^ (prefixWord ++ tailWord_7988637).sum := by decide
  have hdescent : baseEnd_7988637 < baseStart_7988637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988647 : List Nat := [1, 1, 6, 1, 1, 1, 4, 8]
def baseStart_7988647 : Nat := 118140960795 + 7988647 * 2 ^ 59
def prefixEnd_7988647 : Nat := 4983230072969 + 3 ^ 40 * 7988647 * 2
def baseEnd_7988647 : Nat := 151926507040678189465681

theorem tailTrace_7988647 : CollatzResearch.WordTrace tailWord_7988647 prefixEnd_7988647 151926507040678189465681 := by
  unfold tailWord_7988647
  simp only [CollatzResearch.WordTrace]
  refine ⟨291369893089503746131076195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194246595393002497420717463 291369893089503746131076195)
  ·
    refine ⟨437054839634255619196614293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291369893089503746131076195 437054839634255619196614293)
    ·
      refine ⟨20486945607855732149841295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 437054839634255619196614293 20486945607855732149841295)
      ·
        refine ⟨30730418411783598224761943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20486945607855732149841295 30730418411783598224761943)
        ·
          refine ⟨46095627617675397337142915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730418411783598224761943 46095627617675397337142915)
          ·
            refine ⟨69143441426513096005714373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46095627617675397337142915 69143441426513096005714373)
            ·
              refine ⟨12964395267471205501071445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69143441426513096005714373 12964395267471205501071445)
              ·
                refine ⟨151926507040678189465681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12964395267471205501071445 151926507040678189465681)
                ·
                  rfl

theorem cell23_7988647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 8].length) (baseStart_7988647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988647 prefixEnd_7988647 := by exact prefixLift 7988647
  have htrace : WordTrace (prefixWord ++ tailWord_7988647) baseStart_7988647 baseEnd_7988647 := by
    simpa [prefixWord, tailWord_7988647, baseEnd_7988647] using wordTrace_append hprefix tailTrace_7988647
  have hstable : (prefixWord ++ tailWord_7988647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988647).length < 2 ^ (prefixWord ++ tailWord_7988647).sum := by decide
  have hdescent : baseEnd_7988647 < baseStart_7988647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988661 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7988661 : Nat := 118140960795 + 7988661 * 2 ^ 59
def prefixEnd_7988661 : Nat := 4983230072969 + 3 ^ 40 * 7988661 * 2
def baseEnd_7988661 : Nat := 4102022878827474060798323

theorem tailTrace_7988661 : CollatzResearch.WordTrace tailWord_7988661 prefixEnd_7988661 4102022878827474060798323 := by
  unfold tailWord_7988661
  simp only [CollatzResearch.WordTrace]
  refine ⟨291370403711453026522085837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194246935807635351014723891 291370403711453026522085837)
  ·
    refine ⟨109263901391794884945782189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291370403711453026522085837 109263901391794884945782189)
    ·
      refine ⟨40973963021923081854668321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109263901391794884945782189 40973963021923081854668321)
      ·
        refine ⟨30730472266442311391001241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40973963021923081854668321 30730472266442311391001241)
        ·
          refine ⟨23047854199831733543250931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30730472266442311391001241 23047854199831733543250931)
          ·
            refine ⟨34571781299747600314876397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047854199831733543250931 34571781299747600314876397)
            ·
              refine ⟨12964417987405350118078649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34571781299747600314876397 12964417987405350118078649)
              ·
                refine ⟨9723313490554012588558987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12964417987405350118078649 9723313490554012588558987)
                ·
                  refine ⟨14584970235831018882838481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723313490554012588558987 14584970235831018882838481)
                  ·
                    refine ⟨10938727676873264162128861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14584970235831018882838481 10938727676873264162128861)
                    ·
                      refine ⟨4102022878827474060798323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938727676873264162128861 4102022878827474060798323)
                      ·
                        rfl

theorem cell23_7988661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7988661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988661 prefixEnd_7988661 := by exact prefixLift 7988661
  have htrace : WordTrace (prefixWord ++ tailWord_7988661) baseStart_7988661 baseEnd_7988661 := by
    simpa [prefixWord, tailWord_7988661, baseEnd_7988661] using wordTrace_append hprefix tailTrace_7988661
  have hstable : (prefixWord ++ tailWord_7988661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988661).length < 2 ^ (prefixWord ++ tailWord_7988661).sum := by decide
  have hdescent : baseEnd_7988661 < baseStart_7988661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988694 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7988694 : Nat := 118140960795 + 7988694 * 2 ^ 59
def prefixEnd_7988694 : Nat := 4983230072969 + 3 ^ 40 * 7988694 * 2
def baseEnd_7988694 : Nat := 1367346607896357477228557

theorem tailTrace_7988694 : CollatzResearch.WordTrace tailWord_7988694 prefixEnd_7988694 1367346607896357477228557 := by
  unfold tailWord_7988694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210725457520842072377321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194247738213555648772024757 18210725457520842072377321)
  ·
    refine ⟨13658044093140631554282991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18210725457520842072377321 13658044093140631554282991)
    ·
      refine ⟨20487066139710947331424487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13658044093140631554282991 20487066139710947331424487)
      ·
        refine ⟨30730599209566420997136731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487066139710947331424487 30730599209566420997136731)
        ·
          refine ⟨46095898814349631495705097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730599209566420997136731 46095898814349631495705097)
          ·
            refine ⟨34571924110762223621778823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46095898814349631495705097 34571924110762223621778823)
            ·
              refine ⟨51857886166143335432668235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571924110762223621778823 51857886166143335432668235)
              ·
                refine ⟨77786829249215003149002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51857886166143335432668235 77786829249215003149002353)
                ·
                  refine ⟨58340121936911252361751765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77786829249215003149002353 58340121936911252361751765)
                  ·
                    refine ⟨1367346607896357477228557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58340121936911252361751765 1367346607896357477228557)
                    ·
                      rfl

theorem cell23_7988694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7988694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988694 prefixEnd_7988694 := by exact prefixLift 7988694
  have htrace : WordTrace (prefixWord ++ tailWord_7988694) baseStart_7988694 baseEnd_7988694 := by
    simpa [prefixWord, tailWord_7988694, baseEnd_7988694] using wordTrace_append hprefix tailTrace_7988694
  have hstable : (prefixWord ++ tailWord_7988694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988694).length < 2 ^ (prefixWord ++ tailWord_7988694).sum := by decide
  have hdescent : baseEnd_7988694 < baseStart_7988694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988697 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_7988697 : Nat := 118140960795 + 7988697 * 2 ^ 59
def prefixEnd_7988697 : Nat := 4983230072969 + 3 ^ 40 * 7988697 * 2
def baseEnd_7988697 : Nat := 4102041364131035919948157

theorem tailTrace_7988697 : CollatzResearch.WordTrace tailWord_7988697 prefixEnd_7988697 4102041364131035919948157 := by
  unfold tailWord_7988697
  simp only [CollatzResearch.WordTrace]
  refine ⟨291371716739322604670396345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194247811159548403113597563 291371716739322604670396345)
  ·
    refine ⟨218528787554491953502797259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291371716739322604670396345 218528787554491953502797259)
    ·
      refine ⟨327793181331737930254195889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218528787554491953502797259 327793181331737930254195889)
      ·
        refine ⟨245844885998803447690646917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327793181331737930254195889 245844885998803447690646917)
        ·
          refine ⟨46095916124775646441996297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245844885998803447690646917 46095916124775646441996297)
          ·
            refine ⟨34571937093581734831497223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46095916124775646441996297 34571937093581734831497223)
            ·
              refine ⟨51857905640372602247245835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571937093581734831497223 51857905640372602247245835)
              ·
                refine ⟨77786858460558903370868753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51857905640372602247245835 77786858460558903370868753)
                ·
                  refine ⟨58340143845419177528151565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77786858460558903370868753 58340143845419177528151565)
                  ·
                    refine ⟨21877553942032191573056837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58340143845419177528151565 21877553942032191573056837)
                    ·
                      refine ⟨4102041364131035919948157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21877553942032191573056837 4102041364131035919948157)
                      ·
                        rfl

theorem cell23_7988697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_7988697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988697 prefixEnd_7988697 := by exact prefixLift 7988697
  have htrace : WordTrace (prefixWord ++ tailWord_7988697) baseStart_7988697 baseEnd_7988697 := by
    simpa [prefixWord, tailWord_7988697, baseEnd_7988697] using wordTrace_append hprefix tailTrace_7988697
  have hstable : (prefixWord ++ tailWord_7988697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988697).length < 2 ^ (prefixWord ++ tailWord_7988697).sum := by decide
  have hdescent : baseEnd_7988697 < baseStart_7988697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988701 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7988701 : Nat := 118140960795 + 7988701 * 2 ^ 59
def prefixEnd_7988701 : Nat := 4983230072969 + 3 ^ 40 * 7988701 * 2
def baseEnd_7988701 : Nat := 4102043418053653904298139

theorem tailTrace_7988701 : CollatzResearch.WordTrace tailWord_7988701 prefixEnd_7988701 4102043418053653904298139 := by
  unfold tailWord_7988701
  simp only [CollatzResearch.WordTrace]
  refine ⟨291371862631308113353541957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194247908420872075569027971 291371862631308113353541957)
  ·
    refine ⟨54632224243370271253789117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291371862631308113353541957 54632224243370271253789117)
    ·
      refine ⟨20487084091263851720170919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54632224243370271253789117 20487084091263851720170919)
      ·
        refine ⟨30730626136895777580256379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487084091263851720170919 30730626136895777580256379)
        ·
          refine ⟨46095939205343666370384569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730626136895777580256379 46095939205343666370384569)
          ·
            refine ⟨34571954404007749777788427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46095939205343666370384569 34571954404007749777788427)
            ·
              refine ⟨51857931606011624666682641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571954404007749777788427 51857931606011624666682641)
              ·
                refine ⟨38893448704508718500011981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51857931606011624666682641 38893448704508718500011981)
                ·
                  refine ⟨14585043264190769437504493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38893448704508718500011981 14585043264190769437504493)
                  ·
                    refine ⟨5469391224071538539064185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14585043264190769437504493 5469391224071538539064185)
                    ·
                      refine ⟨4102043418053653904298139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469391224071538539064185 4102043418053653904298139)
                      ·
                        rfl

theorem cell23_7988701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7988701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988701 prefixEnd_7988701 := by exact prefixLift 7988701
  have htrace : WordTrace (prefixWord ++ tailWord_7988701) baseStart_7988701 baseEnd_7988701 := by
    simpa [prefixWord, tailWord_7988701, baseEnd_7988701] using wordTrace_append hprefix tailTrace_7988701
  have hstable : (prefixWord ++ tailWord_7988701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988701).length < 2 ^ (prefixWord ++ tailWord_7988701).sum := by decide
  have hdescent : baseEnd_7988701 < baseStart_7988701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988707 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 8]
def baseStart_7988707 : Nat := 118140960795 + 7988707 * 2 ^ 59
def prefixEnd_7988707 : Nat := 4983230072969 + 3 ^ 40 * 7988707 * 2
def baseEnd_7988707 : Nat := 1367348832979193626941037

theorem tailTrace_7988707 : CollatzResearch.WordTrace tailWord_7988707 prefixEnd_7988707 1367348832979193626941037 := by
  unfold tailWord_7988707
  simp only [CollatzResearch.WordTrace]
  refine ⟨291372081469286376378260375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194248054312857584252173583 291372081469286376378260375)
  ·
    refine ⟨437058122203929564567390563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291372081469286376378260375 437058122203929564567390563)
    ·
      refine ⟨655587183305894346851085845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437058122203929564567390563 655587183305894346851085845)
      ·
        refine ⟨30730649217463797508644649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 655587183305894346851085845 30730649217463797508644649)
        ·
          refine ⟨23047986913097848131483487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30730649217463797508644649 23047986913097848131483487)
          ·
            refine ⟨34571980369646772197225231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047986913097848131483487 34571980369646772197225231)
            ·
              refine ⟨51857970554470158295837847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34571980369646772197225231 51857970554470158295837847)
              ·
                refine ⟨77786955831705237443756771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51857970554470158295837847 77786955831705237443756771)
                ·
                  refine ⟨116680433747557856165635157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77786955831705237443756771 116680433747557856165635157)
                  ·
                    refine ⟨1367348832979193626941037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116680433747557856165635157 1367348832979193626941037)
                    ·
                      rfl

theorem cell23_7988707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_7988707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988707 prefixEnd_7988707 := by exact prefixLift 7988707
  have htrace : WordTrace (prefixWord ++ tailWord_7988707) baseStart_7988707 baseEnd_7988707 := by
    simpa [prefixWord, tailWord_7988707, baseEnd_7988707] using wordTrace_append hprefix tailTrace_7988707
  have hstable : (prefixWord ++ tailWord_7988707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988707).length < 2 ^ (prefixWord ++ tailWord_7988707).sum := by decide
  have hdescent : baseEnd_7988707 < baseStart_7988707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
